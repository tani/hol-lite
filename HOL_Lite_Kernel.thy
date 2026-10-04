theory HOL_Lite_Kernel
  imports Main "HOL-Library.Code_Target_Nat" "HOL-Library.Monad_Syntax"
begin

text \<open>
  A port of HOL Light's logical kernel (@{text fusion.ml}) to Isabelle/HOL.

  Types, terms, theorems and the ten primitive inference rules of HOL Light are
  reproduced function by function.  OCaml's exceptions become @{typ "'a option"}, and
  OCaml's global references (@{text the_type_constants}, @{text the_term_constants},
  @{text the_axioms}, @{text the_definitions}) are threaded explicitly through a
  @{text kstate} record.  Theorems are values @{text "Sequent hyps concl"} built only by
  the kernel functions of this file; the rest of the development constructs theorems
  exclusively through them, as in an LCF-style prover.

  The two places where OCaml relies on non-structural recursion are ported without fuel:
  @{text variant} is a total function whose termination is proved (the name grows by one
  prime per step while all names occurring in the avoided terms have bounded length), and
  the capture-avoiding retry in @{text inst} is a @{text partial_function} into @{typ "'a option"},
  where @{text None} stands for non-termination.
\<close>

section \<open>Utilities\<close>

datatype cmp = CLt | CEq | CGt

fun cmp_nat :: "nat \<Rightarrow> nat \<Rightarrow> cmp" where
  "cmp_nat a b = (if a < b then CLt else if a = b then CEq else CGt)"

fun cmp_list :: "nat list \<Rightarrow> nat list \<Rightarrow> cmp" where
  "cmp_list [] [] = CEq"
| "cmp_list [] (_ # _) = CLt"
| "cmp_list (_ # _) [] = CGt"
| "cmp_list (a # as) (b # bs) = (case cmp_nat a b of CEq \<Rightarrow> cmp_list as bs | c \<Rightarrow> c)"

definition ser_str :: "string \<Rightarrow> nat list" where
  "ser_str s = length s # map (\<lambda>c. of_char c) s"

definition rev_assocd :: "'a \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "rev_assocd a l d = (case find (\<lambda>p. snd p = a) l of Some p \<Rightarrow> fst p | None \<Rightarrow> d)"

definition lsubtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "lsubtract l1 l2 = filter (\<lambda>x. x \<notin> set l2) l1"

section \<open>Types\<close>

datatype hol_type = Tyvar string | Tyapp string "hol_type list"

primrec ser_ty :: "hol_type \<Rightarrow> nat list" where
  "ser_ty (Tyvar v) = 0 # ser_str v"
| "ser_ty (Tyapp c args) = 1 # ser_str c @ [length args] @ concat (map ser_ty args)"

definition cmp_ty :: "hol_type \<Rightarrow> hol_type \<Rightarrow> cmp" where
  "cmp_ty a b = cmp_list (ser_ty a) (ser_ty b)"

definition bool_ty :: hol_type where "bool_ty = Tyapp ''bool'' []"
definition aty :: hol_type where "aty = Tyvar ''A''"
definition fun_ty :: "hol_type \<Rightarrow> hol_type \<Rightarrow> hol_type" where "fun_ty a b = Tyapp ''fun'' [a, b]"

primrec tyvars :: "hol_type \<Rightarrow> hol_type list" where
  "tyvars (Tyvar v) = [Tyvar v]"
| "tyvars (Tyapp c args) = foldr List.union (map tyvars args) []"

primrec type_subst :: "(hol_type \<times> hol_type) list \<Rightarrow> hol_type \<Rightarrow> hol_type" where
  "type_subst i (Tyvar v) = rev_assocd (Tyvar v) i (Tyvar v)"
| "type_subst i (Tyapp c args) = Tyapp c (map (type_subst i) args)"

fun dest_fun_ty :: "hol_type \<Rightarrow> (hol_type \<times> hol_type) option" where
  "dest_fun_ty (Tyapp c [a, b]) = (if c = ''fun'' then Some (a, b) else None)"
| "dest_fun_ty _ = None"

section \<open>Terms\<close>

datatype hterm = Var string hol_type | Const string hol_type | Comb hterm hterm | Abs hterm hterm

primrec ser_tm :: "hterm \<Rightarrow> nat list" where
  "ser_tm (Var n ty) = 0 # ser_str n @ ser_ty ty"
| "ser_tm (Const n ty) = 1 # ser_str n @ ser_ty ty"
| "ser_tm (Comb s t) = 2 # ser_tm s @ ser_tm t"
| "ser_tm (Abs v t) = 3 # ser_tm v @ ser_tm t"

definition cmp_tm :: "hterm \<Rightarrow> hterm \<Rightarrow> cmp" where
  "cmp_tm a b = cmp_list (ser_tm a) (ser_tm b)"

definition bad_ty :: hol_type where "bad_ty = Tyvar []"

primrec type_of :: "hterm \<Rightarrow> hol_type" where
  "type_of (Var _ ty) = ty"
| "type_of (Const _ ty) = ty"
| "type_of (Comb s _) = (case type_of s of Tyapp _ (_ # b # _) \<Rightarrow> b | _ \<Rightarrow> bad_ty)"
| "type_of (Abs v t) = (case v of Var _ ty \<Rightarrow> fun_ty ty (type_of t) | _ \<Rightarrow> bad_ty)"

primrec tm_size :: "hterm \<Rightarrow> nat" where
  "tm_size (Var _ _) = 1"
| "tm_size (Const _ _) = 1"
| "tm_size (Comb s t) = Suc (tm_size s + tm_size t)"
| "tm_size (Abs v t) = Suc (tm_size v + tm_size t)"

primrec frees :: "hterm \<Rightarrow> hterm list" where
  "frees (Var n ty) = [Var n ty]"
| "frees (Const n ty) = []"
| "frees (Comb s t) = List.union (frees s) (frees t)"
| "frees (Abs bv bod) = lsubtract (frees bod) [bv]"

definition freesl :: "hterm list \<Rightarrow> hterm list" where
  "freesl tml = foldr (\<lambda>t acc. List.union (frees t) acc) tml []"

primrec freesin :: "hterm list \<Rightarrow> hterm \<Rightarrow> bool" where
  "freesin acc (Var n ty) = (Var n ty \<in> set acc)"
| "freesin acc (Const n ty) = True"
| "freesin acc (Comb s t) = (freesin acc s \<and> freesin acc t)"
| "freesin acc (Abs bv bod) = freesin (bv # acc) bod"

primrec vfree_in :: "hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "vfree_in v (Var n ty) = (Var n ty = v)"
| "vfree_in v (Const n ty) = (Const n ty = v)"
| "vfree_in v (Comb s t) = (vfree_in v s \<or> vfree_in v t)"
| "vfree_in v (Abs bv bod) = (v \<noteq> bv \<and> vfree_in v bod)"

primrec type_vars_in_term :: "hterm \<Rightarrow> hol_type list" where
  "type_vars_in_term (Var _ ty) = tyvars ty"
| "type_vars_in_term (Const _ ty) = tyvars ty"
| "type_vars_in_term (Comb s t) = List.union (type_vars_in_term s) (type_vars_in_term t)"
| "type_vars_in_term (Abs v t) = List.union (type_vars_in_term v) (type_vars_in_term t)"

text \<open>@{text variant}: rename a variable by appending primes until it is not free in any
  term of @{text avoid}.  Termination: every variable free in a term has a name no longer
  than the total length of all names in that term.\<close>

primrec tm_nlen :: "hterm \<Rightarrow> nat" where
  "tm_nlen (Var n _) = length n"
| "tm_nlen (Const n _) = length n"
| "tm_nlen (Comb s t) = tm_nlen s + tm_nlen t"
| "tm_nlen (Abs v t) = tm_nlen v + tm_nlen t"

lemma vfree_in_nlen: "vfree_in (Var s ty) t \<Longrightarrow> length s \<le> tm_nlen t"
  by (induction t) auto

lemma list_ex_nlen:
  "list_ex (vfree_in (Var s ty)) avoid \<Longrightarrow> length s \<le> sum_list (map tm_nlen avoid)"
proof (induction avoid)
  case Nil then show ?case by simp
next
  case (Cons a avoid)
  then show ?case using vfree_in_nlen[of s ty a] by auto
qed

function variant :: "hterm list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "variant avoid v =
     (if \<not> list_ex (vfree_in v) avoid then v
      else case v of Var s ty \<Rightarrow> variant avoid (Var (s @ [CHR 0x27]) ty) | _ \<Rightarrow> v)"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>(avoid, v). sum_list (map tm_nlen avoid) + 1 - (case v of Var s _ \<Rightarrow> length s | _ \<Rightarrow> 0))")
   apply simp
  apply (auto dest: list_ex_nlen split: hterm.splits)
  done

text \<open>Capture-avoiding substitution of terms for variables; @{text ilist} holds pairs
  @{text "(replacement, variable)"}.\<close>

primrec vsubst :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "vsubst ilist (Const n ty) = Const n ty"
| "vsubst ilist (Var n ty) = rev_assocd (Var n ty) ilist (Var n ty)"
| "vsubst ilist (Comb s t) = Comb (vsubst ilist s) (vsubst ilist t)"
| "vsubst ilist (Abs v s) =
     (let ilist' = filter (\<lambda>p. snd p \<noteq> v) ilist in
      if ilist' = [] then Abs v s
      else
        let s' = vsubst ilist' s in
        if s' = s then Abs v s
        else if list_ex (\<lambda>p. vfree_in v (fst p) \<and> vfree_in (snd p) s) ilist'
        then (let v' = variant [s'] v in Abs v' (vsubst ((v', v) # ilist') s))
        else Abs v s')"

definition vsubst_checked :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "vsubst_checked theta tm =
     (if theta = [] then Some tm
      else if list_all (\<lambda>p. (case snd p of Var _ ty \<Rightarrow> type_of (fst p) = ty | _ \<Rightarrow> False)) theta
      then Some (vsubst theta tm) else None)"

text \<open>Type instantiation of terms.  The OCaml @{text Clash} exception is the result
  constructor @{text IClash}.  The capture-avoiding retry is not structurally recursive, so
  @{text inst_f} is a @{text partial_function}; @{text None} is non-termination.\<close>

datatype instres = IOk hterm | IClash hterm

definition inst_var :: "(hol_type \<times> hol_type) list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "inst_var tyin v = (case v of Var n ty \<Rightarrow> Var n (type_subst tyin ty) | _ \<Rightarrow> v)"

partial_function (option) inst_f ::
  "(hterm \<times> hterm) list \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> hterm \<Rightarrow> instres option" where
  "inst_f env tyin tm =
     (case tm of
        Var nm ty \<Rightarrow>
          (let ty' = type_subst tyin ty; tm' = Var nm ty' in
           if rev_assocd tm' env tm = tm then Some (IOk tm') else Some (IClash tm'))
      | Const c ty \<Rightarrow> Some (IOk (Const c (type_subst tyin ty)))
      | Comb f x \<Rightarrow>
          do { rf \<leftarrow> inst_f env tyin f;
               (case rf of
                  IOk f' \<Rightarrow>
                    do { rx \<leftarrow> inst_f env tyin x;
                         (case rx of IOk x' \<Rightarrow> Some (IOk (Comb f' x')) | IClash w \<Rightarrow> Some (IClash w)) }
                | IClash w \<Rightarrow> Some (IClash w)) }
      | Abs y t \<Rightarrow>
          (let y' = inst_var tyin y; env' = (y, y') # env in
           do { rt \<leftarrow> inst_f env' tyin t;
                (case rt of
                   IOk t' \<Rightarrow> Some (IOk (Abs y' t'))
                 | IClash w' \<Rightarrow>
                     if w' \<noteq> y' then Some (IClash w')
                     else
                       (let ifrees = map (inst_var tyin) (frees t);
                            y'' = variant ifrees y'
                        in case (y'', y) of
                             (Var nm2 _, Var _ ty0) \<Rightarrow>
                               inst_f env tyin (Abs (Var nm2 ty0) (vsubst [(Var nm2 ty0, y)] t))
                           | _ \<Rightarrow> None)) }))"

declare inst_f.simps [code]

definition inst :: "(hol_type \<times> hol_type) list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "inst tyin tm =
     (if tyin = [] then Some tm
      else case inst_f [] tyin tm of
             Some (IOk t) \<Rightarrow> Some t | _ \<Rightarrow> None)"

section \<open>Alpha-equivalence\<close>

fun ordav :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> cmp" where
  "ordav [] x1 x2 = cmp_tm x1 x2"
| "ordav ((t1, t2) # oenv) x1 x2 =
     (if cmp_tm x1 t1 = CEq then (if cmp_tm x2 t2 = CEq then CEq else CLt)
      else if cmp_tm x2 t2 = CEq then CGt
      else ordav oenv x1 x2)"

definition rank :: "hterm \<Rightarrow> nat" where
  "rank t = (case t of Const _ _ \<Rightarrow> 0 | Var _ _ \<Rightarrow> 1 | Comb _ _ \<Rightarrow> 2 | Abs _ _ \<Rightarrow> 3)"

fun orda :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> cmp" where
  "orda env (Var a b) (Var c d) = ordav env (Var a b) (Var c d)"
| "orda env (Const a b) (Const c d) = cmp_tm (Const a b) (Const c d)"
| "orda env (Comb s1 t1) (Comb s2 t2) =
     (case orda env s1 s2 of CEq \<Rightarrow> orda env t1 t2 | c \<Rightarrow> c)"
| "orda env (Abs (Var n1 ty1) t1) (Abs (Var n2 ty2) t2) =
     (case cmp_ty ty1 ty2 of
        CEq \<Rightarrow> orda ((Var n1 ty1, Var n2 ty2) # env) t1 t2
      | c \<Rightarrow> c)"
| "orda env a b = cmp_nat (rank a) (rank b)"

definition alphaorder :: "hterm \<Rightarrow> hterm \<Rightarrow> cmp" where
  "alphaorder = orda []"

definition aconv :: "hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "aconv s t = (alphaorder s t = CEq)"

fun term_remove :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "term_remove tm [] = []"
| "term_remove tm (s # ss) =
     (case alphaorder tm s of
        CGt \<Rightarrow> s # term_remove tm ss
      | CEq \<Rightarrow> ss
      | CLt \<Rightarrow> s # ss)"

fun term_union :: "hterm list \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "term_union [] l2 = l2"
| "term_union l1 [] = l1"
| "term_union (h1 # t1) (h2 # t2) =
     (case alphaorder h1 h2 of
        CEq \<Rightarrow> h1 # term_union t1 t2
      | CLt \<Rightarrow> h1 # term_union t1 (h2 # t2)
      | CGt \<Rightarrow> h2 # term_union (h1 # t1) t2)"

fun term_image :: "(hterm \<Rightarrow> hterm option) \<Rightarrow> hterm list \<Rightarrow> hterm list option" where
  "term_image f [] = Some []"
| "term_image f (h # t) =
     (case f h of
        None \<Rightarrow> None
      | Some h' \<Rightarrow> (case term_image f t of None \<Rightarrow> None | Some t' \<Rightarrow> Some (term_union [h'] t')))"

section \<open>Kernel state\<close>

datatype hthm = Sequent "hterm list" hterm

fun hyp :: "hthm \<Rightarrow> hterm list" where "hyp (Sequent asl _) = asl"
fun concl :: "hthm \<Rightarrow> hterm" where "concl (Sequent _ c) = c"

record kstate =
  the_type_constants :: "(string \<times> nat) list"
  the_term_constants :: "(string \<times> hol_type) list"
  the_axioms :: "hthm list"
  the_definitions :: "hthm list"

definition init_kstate :: kstate where
  "init_kstate =
     \<lparr> the_type_constants = [(''bool'', 0), (''fun'', 2)],
       the_term_constants = [(''='', fun_ty aty (fun_ty aty bool_ty))],
       the_axioms = [],
       the_definitions = [] \<rparr>"

definition get_type_arity :: "kstate \<Rightarrow> string \<Rightarrow> nat option" where
  "get_type_arity ks s = map_of (the_type_constants ks) s"

definition get_const_type :: "kstate \<Rightarrow> string \<Rightarrow> hol_type option" where
  "get_const_type ks s = map_of (the_term_constants ks) s"

definition new_type :: "kstate \<Rightarrow> string \<times> nat \<Rightarrow> kstate option" where
  "new_type ks p =
     (case get_type_arity ks (fst p) of
        Some _ \<Rightarrow> None
      | None \<Rightarrow> Some (ks\<lparr> the_type_constants := p # the_type_constants ks \<rparr>))"

definition new_constant :: "kstate \<Rightarrow> string \<times> hol_type \<Rightarrow> kstate option" where
  "new_constant ks p =
     (case get_const_type ks (fst p) of
        Some _ \<Rightarrow> None
      | None \<Rightarrow> Some (ks\<lparr> the_term_constants := p # the_term_constants ks \<rparr>))"

definition mk_type :: "kstate \<Rightarrow> string \<Rightarrow> hol_type list \<Rightarrow> hol_type option" where
  "mk_type ks tyop args =
     (case get_type_arity ks tyop of
        Some arity \<Rightarrow> if arity = length args then Some (Tyapp tyop args) else None
      | None \<Rightarrow> None)"

definition mk_const :: "kstate \<Rightarrow> string \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> hterm option" where
  "mk_const ks name theta =
     (case get_const_type ks name of
        Some uty \<Rightarrow> Some (Const name (type_subst theta uty))
      | None \<Rightarrow> None)"

definition mk_comb :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_comb f a =
     (case dest_fun_ty (type_of f) of
        Some (ty, _) \<Rightarrow> if ty = type_of a then Some (Comb f a) else None
      | None \<Rightarrow> None)"

definition mk_abs :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_abs bvar bod = (case bvar of Var _ _ \<Rightarrow> Some (Abs bvar bod) | _ \<Rightarrow> None)"

definition mk_var :: "string \<Rightarrow> hol_type \<Rightarrow> hterm" where
  "mk_var v ty = Var v ty"

fun dest_comb :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_comb (Comb f x) = Some (f, x)" | "dest_comb _ = None"

fun dest_abs :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_abs (Abs v b) = Some (v, b)" | "dest_abs _ = None"

fun dest_var :: "hterm \<Rightarrow> (string \<times> hol_type) option" where
  "dest_var (Var n ty) = Some (n, ty)" | "dest_var _ = None"

fun dest_const :: "hterm \<Rightarrow> (string \<times> hol_type) option" where
  "dest_const (Const n ty) = Some (n, ty)" | "dest_const _ = None"

definition safe_mk_eq :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "safe_mk_eq l r =
     (let ty = type_of l in
      Comb (Comb (Const ''='' (fun_ty ty (fun_ty ty bool_ty))) l) r)"

fun dest_eq :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_eq (Comb (Comb (Const n _) l) r) = (if n = ''='' then Some (l, r) else None)"
| "dest_eq _ = None"

section \<open>Primitive inference rules\<close>

definition REFL :: "hterm \<Rightarrow> hthm" where
  "REFL tm = Sequent [] (safe_mk_eq tm tm)"

fun TRANS :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "TRANS (Sequent asl1 (Comb (Comb (Const n1 t1) l) m1)) (Sequent asl2 (Comb (Comb (Const n2 t2) m2) r)) =
     (if n1 = ''='' \<and> n2 = ''='' \<and> aconv m1 m2
      then Some (Sequent (term_union asl1 asl2) (Comb (Comb (Const n1 t1) l) r))
      else None)"
| "TRANS _ _ = None"

fun MK_COMB :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "MK_COMB (Sequent asl1 (Comb (Comb (Const n1 _) l1) r1)) (Sequent asl2 (Comb (Comb (Const n2 _) l2) r2)) =
     (if n1 = ''='' \<and> n2 = ''=''
      then (case dest_fun_ty (type_of r1) of
              Some (ty, _) \<Rightarrow>
                if ty = type_of r2
                then Some (Sequent (term_union asl1 asl2) (safe_mk_eq (Comb l1 l2) (Comb r1 r2)))
                else None
            | None \<Rightarrow> None)
      else None)"
| "MK_COMB _ _ = None"

fun ABS :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "ABS (Var n ty) (Sequent asl (Comb (Comb (Const c _) l) r)) =
     (if c = ''='' \<and> \<not> list_ex (vfree_in (Var n ty)) asl
      then Some (Sequent asl (safe_mk_eq (Abs (Var n ty) l) (Abs (Var n ty) r)))
      else None)"
| "ABS _ _ = None"

fun BETA :: "hterm \<Rightarrow> hthm option" where
  "BETA (Comb (Abs v bod) arg) =
     (if arg = v then Some (Sequent [] (safe_mk_eq (Comb (Abs v bod) arg) bod)) else None)"
| "BETA _ = None"

definition ASSUME :: "hterm \<Rightarrow> hthm option" where
  "ASSUME tm = (if type_of tm = bool_ty then Some (Sequent [tm] tm) else None)"

fun EQ_MP :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "EQ_MP (Sequent asl1 (Comb (Comb (Const c _) l) r)) (Sequent asl2 c2) =
     (if c = ''='' \<and> aconv l c2 then Some (Sequent (term_union asl1 asl2) r) else None)"
| "EQ_MP _ _ = None"

fun DEDUCT_ANTISYM_RULE :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm" where
  "DEDUCT_ANTISYM_RULE (Sequent asl1 c1) (Sequent asl2 c2) =
     Sequent (term_union (term_remove c2 asl1) (term_remove c1 asl2)) (safe_mk_eq c1 c2)"

fun INST_TYPE :: "(hol_type \<times> hol_type) list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "INST_TYPE theta (Sequent asl c) =
     (case term_image (inst theta) asl of
        Some asl' \<Rightarrow> (case inst theta c of Some c' \<Rightarrow> Some (Sequent asl' c') | None \<Rightarrow> None)
      | None \<Rightarrow> None)"

fun INST :: "(hterm \<times> hterm) list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "INST theta (Sequent asl c) =
     (case term_image (vsubst_checked theta) asl of
        Some asl' \<Rightarrow> (case vsubst_checked theta c of Some c' \<Rightarrow> Some (Sequent asl' c') | None \<Rightarrow> None)
      | None \<Rightarrow> None)"

section \<open>Extension principles\<close>

definition new_axiom :: "kstate \<Rightarrow> hterm \<Rightarrow> (kstate \<times> hthm) option" where
  "new_axiom ks tm =
     (if type_of tm = bool_ty
      then (let th = Sequent [] tm in Some (ks\<lparr> the_axioms := th # the_axioms ks \<rparr>, th))
      else None)"

definition new_basic_definition :: "kstate \<Rightarrow> hterm \<Rightarrow> (kstate \<times> hthm) option" where
  "new_basic_definition ks tm =
     (case tm of
        Comb (Comb (Const eq _) (Var cname ty)) r \<Rightarrow>
          if eq \<noteq> ''='' then None
          else if \<not> freesin [] r then None
          else if \<not> set (type_vars_in_term r) \<subseteq> set (tyvars ty) then None
          else
            (case new_constant ks (cname, ty) of
               None \<Rightarrow> None
             | Some ks' \<Rightarrow>
                 (let dth = Sequent [] (safe_mk_eq (Const cname ty) r)
                  in Some (ks'\<lparr> the_definitions := dth # the_definitions ks' \<rparr>, dth)))
      | _ \<Rightarrow> None)"

fun isort :: "hol_type list \<Rightarrow> hol_type list" where
  "isort [] = []"
| "isort (x # xs) =
     (let ys = isort xs in
      takeWhile (\<lambda>y. cmp_ty y x = CLt) ys @ [x] @ dropWhile (\<lambda>y. cmp_ty y x = CLt) ys)"

definition new_basic_type_definition ::
  "kstate \<Rightarrow> string \<Rightarrow> string \<times> string \<Rightarrow> hthm \<Rightarrow> (kstate \<times> hthm \<times> hthm) option" where
  "new_basic_type_definition ks tyname names th =
     (case names of (absname, repname) \<Rightarrow>
      (case th of Sequent asl c \<Rightarrow>
        if get_const_type ks absname \<noteq> None \<or> get_const_type ks repname \<noteq> None then None
        else if asl \<noteq> [] then None
        else
          (case c of
             Comb P x \<Rightarrow>
               if \<not> freesin [] P then None
               else
                 (let tvs = isort (type_vars_in_term P) in
                  case new_type ks (tyname, length tvs) of
                    None \<Rightarrow> None
                  | Some ks1 \<Rightarrow>
                      (let aty' = Tyapp tyname tvs; rty = type_of x;
                           absty = fun_ty rty aty'; repty = fun_ty aty' rty
                       in case new_constant ks1 (absname, absty) of
                            None \<Rightarrow> None
                          | Some ks2 \<Rightarrow>
                              (case new_constant ks2 (repname, repty) of
                                 None \<Rightarrow> None
                               | Some ks3 \<Rightarrow>
                                   (let abs' = Const absname absty; rep' = Const repname repty;
                                        a = Var ''a'' aty'; r = Var ''r'' rty
                                    in Some (ks3,
                                       Sequent [] (safe_mk_eq (Comb abs' (Comb rep' a)) a),
                                       Sequent [] (safe_mk_eq (Comb P r)
                                                     (safe_mk_eq (Comb rep' (Comb abs' r)) r)))))))
           | _ \<Rightarrow> None)))"

end
