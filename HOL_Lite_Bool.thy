theory HOL_Lite_Bool
  imports HOL_Lite_Kernel
begin

text \<open>
  Ports of the derived layers of HOL Light that sit on top of @{text fusion.ml}:

  @{text basics.ml} (term utilities), @{text equal.ml} (conversions and conversionals),
  @{text bool.ml} (the logical constants and their rules), @{text drule.ml}
  (higher-order @{text term_match}, @{text INSTANTIATE}, @{text PART_MATCH}),
  @{text simp.ml} (@{text REWR_CONV}, @{text REWRITE_CONV}, @{text GEN_REWRITE_CONV}),
  @{text tactics.ml} (the subset needed here) and @{text class.ml} (@{text TAUT}).

  OCaml exceptions are @{typ "'a option"}.  The functions whose OCaml definitions are not
  structurally recursive (@{text REPEATC} and the depth conversions, @{text term_homatch})
  are @{text partial_function}s into @{typ "'a option option"}: the outer @{text None} is
  non-termination, the inner @{text None} is an OCaml failure.  Constants are named in ASCII
  (@{text T}, @{text F}, @{text NOT}, @{text AND}, @{text OR}, @{text IMP}, @{text ALL},
  @{text EX}, @{text EXU}).  The classical axiom @{text BOOL_CASES_AX} is taken as an axiom
  (HOL Light derives it from the axiom of choice in @{text class.ml}).
\<close>

section \<open>Basics (basics.ml)\<close>

type_synonym conv = "hterm \<Rightarrow> hthm option"

fun nat_str :: "nat \<Rightarrow> string" where
  "nat_str n = (if n < 10 then [char_of (48 + n)] else nat_str (n div 10) @ [char_of (48 + n mod 10)])"

definition rev_assoc :: "'a \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'b option" where
  "rev_assoc x l = map_option fst (find (\<lambda>p. snd p = x) l)"

definition rator :: "hterm \<Rightarrow> hterm option" where
  "rator tm = map_option fst (dest_comb tm)"

definition rand :: "hterm \<Rightarrow> hterm option" where
  "rand tm = map_option snd (dest_comb tm)"

definition lhand :: "hterm \<Rightarrow> hterm option" where
  "lhand tm = Option.bind (rator tm) rand"

definition lhs :: "hthm \<Rightarrow> hterm option" where
  "lhs th = map_option fst (dest_eq (concl th))"

definition rhs :: "hthm \<Rightarrow> hterm option" where
  "rhs th = map_option snd (dest_eq (concl th))"

definition bndvar :: "hterm \<Rightarrow> hterm option" where
  "bndvar tm = map_option fst (dest_abs tm)"

definition body :: "hterm \<Rightarrow> hterm option" where
  "body tm = map_option snd (dest_abs tm)"

definition bb_ty :: hol_type where "bb_ty = fun_ty bool_ty bool_ty"
definition bbb_ty :: hol_type where "bbb_ty = fun_ty bool_ty (fun_ty bool_ty bool_ty)"

definition mk_eq :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_eq l r = (if type_of l = type_of r then Some (safe_mk_eq l r) else None)"

definition list_mk_comb :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm option" where
  "list_mk_comb h args = foldl (\<lambda>acc a. do { f \<leftarrow> acc; mk_comb f a }) (Some h) args"

definition list_mk_abs :: "hterm list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "list_mk_abs vs bod = foldr (\<lambda>v acc. do { b \<leftarrow> acc; mk_abs v b }) vs (Some bod)"

fun strip_comb :: "hterm \<Rightarrow> hterm \<times> hterm list" where
  "strip_comb (Comb f x) = (case strip_comb f of (h, args) \<Rightarrow> (h, args @ [x]))"
| "strip_comb tm = (tm, [])"

fun is_var :: "hterm \<Rightarrow> bool" where
  "is_var (Var _ _) = True" | "is_var _ = False"

fun is_const :: "hterm \<Rightarrow> bool" where
  "is_const (Const _ _) = True" | "is_const _ = False"

fun is_abs :: "hterm \<Rightarrow> bool" where
  "is_abs (Abs _ _) = True" | "is_abs _ = False"

fun is_comb :: "hterm \<Rightarrow> bool" where
  "is_comb (Comb _ _) = True" | "is_comb _ = False"

primrec strip_abs_n :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_abs_n 0 tm = ([], tm)"
| "strip_abs_n (Suc k) tm =
     (case tm of Abs v b \<Rightarrow> (case strip_abs_n k b of (vs, bd) \<Rightarrow> (v # vs, bd)) | _ \<Rightarrow> ([], tm))"

definition strip_abs :: "hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_abs tm = strip_abs_n (tm_size tm) tm"

fun dest_binary :: "string \<Rightarrow> hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_binary c (Comb (Comb (Const n _) l) r) = (if n = c then Some (l, r) else None)"
| "dest_binary _ _ = None"

definition is_binary :: "string \<Rightarrow> hterm \<Rightarrow> bool" where
  "is_binary c tm = (dest_binary c tm \<noteq> None)"

fun dest_binder :: "string \<Rightarrow> hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_binder c (Comb (Const n _) (Abs x t)) = (if n = c then Some (x, t) else None)"
| "dest_binder _ _ = None"

definition is_binder :: "string \<Rightarrow> hterm \<Rightarrow> bool" where
  "is_binder c tm = (dest_binder c tm \<noteq> None)"

text \<open>@{text variables}: all variables, free and bound.\<close>

primrec variables :: "hterm \<Rightarrow> hterm list" where
  "variables (Var n ty) = [Var n ty]"
| "variables (Const n ty) = []"
| "variables (Comb s t) = List.union (variables s) (variables t)"
| "variables (Abs v b) = List.insert v (variables b)"

primrec variants :: "hterm list \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "variants av [] = []"
| "variants av (v # vs) = (let vh = variant av v in vh # variants (vh # av) vs)"

text \<open>@{text genvar}: HOL Light draws names from a global counter; here a name that avoids
  the variables of the given terms is chosen deterministically.\<close>

definition var_name :: "hterm \<Rightarrow> string" where
  "var_name t = (case t of Var n _ \<Rightarrow> n | _ \<Rightarrow> [])"

primrec genvar_n :: "nat \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> hol_type \<Rightarrow> hterm" where
  "genvar_n 0 k used ty = Var (''_'' @ nat_str k) ty"
| "genvar_n (Suc f) k used ty =
     (if (''_'' @ nat_str k) \<in> set used then genvar_n f (Suc k) used ty
      else Var (''_'' @ nat_str k) ty)"

definition genvar :: "hterm list \<Rightarrow> hol_type \<Rightarrow> hterm" where
  "genvar avoid ty =
     (let used = map var_name (concat (map variables avoid)) in genvar_n (length used + 1) 0 used ty)"

definition alpha :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "alpha v tm =
     (case tm of
        Abs v0 bod \<Rightarrow>
          (if v = v0 then Some tm
           else if type_of v = type_of v0 \<and> \<not> vfree_in v bod then mk_abs v (vsubst [(v, v0)] bod)
           else None)
      | _ \<Rightarrow> None)"

text \<open>General substitution for any free expression.\<close>

primrec ssubst :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "ssubst ilist (Var n ty) =
     (if ilist = [] then Some (Var n ty)
      else case find (\<lambda>p. aconv (Var n ty) (snd p)) ilist of
             Some p \<Rightarrow> Some (fst p) | None \<Rightarrow> Some (Var n ty))"
| "ssubst ilist (Const n ty) =
     (if ilist = [] then Some (Const n ty)
      else case find (\<lambda>p. aconv (Const n ty) (snd p)) ilist of
             Some p \<Rightarrow> Some (fst p) | None \<Rightarrow> Some (Const n ty))"
| "ssubst ilist (Comb f x) =
     (if ilist = [] then Some (Comb f x)
      else case find (\<lambda>p. aconv (Comb f x) (snd p)) ilist of
             Some p \<Rightarrow> Some (fst p)
           | None \<Rightarrow> do { f' \<leftarrow> ssubst ilist f; x' \<leftarrow> ssubst ilist x; mk_comb f' x' })"
| "ssubst ilist (Abs v bod) =
     (if ilist = [] then Some (Abs v bod)
      else case find (\<lambda>p. aconv (Abs v bod) (snd p)) ilist of
             Some p \<Rightarrow> Some (fst p)
           | None \<Rightarrow>
               (let ilist' = filter (\<lambda>p. \<not> vfree_in v (snd p)) ilist
                in do { b' \<leftarrow> ssubst ilist' bod; mk_abs v b' }))"

definition subst :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "subst ilist tm =
     (let theta = filter (\<lambda>p. fst p \<noteq> snd p) ilist in
      if theta = [] then Some tm
      else
        let ts = map fst theta; xs = map snd theta;
            gs = variants (variables tm) (snd (foldl (\<lambda>(av, acc) x. (let g = genvar (av @ [tm]) (type_of x) in (av @ [g], acc @ [g])))
                                                    ([], []) xs))
        in do { tm' \<leftarrow> ssubst (zip gs xs) tm;
                (if tm' = tm then Some tm else vsubst_checked (zip ts gs) tm') })"

text \<open>Type matching.\<close>

fun type_match :: "hol_type \<Rightarrow> hol_type \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> (hol_type \<times> hol_type) list option"
and type_match_l :: "hol_type list \<Rightarrow> hol_type list \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> (hol_type \<times> hol_type) list option"
where
  "type_match (Tyvar v) cty sofar =
     (case rev_assoc (Tyvar v) sofar of
        Some c \<Rightarrow> if c = cty then Some sofar else None
      | None \<Rightarrow> Some ((cty, Tyvar v) # sofar))"
| "type_match (Tyapp vop vargs) cty sofar =
     (case cty of
        Tyapp cop cargs \<Rightarrow> if vop = cop then type_match_l vargs cargs sofar else None
      | Tyvar _ \<Rightarrow> None)"
| "type_match_l [] [] sofar = Some sofar"
| "type_match_l (v # vs) (c # cs) sofar =
     (case type_match_l vs cs sofar of None \<Rightarrow> None | Some s \<Rightarrow> type_match v c s)"
| "type_match_l _ _ sofar = None"

definition thm_frees :: "hthm \<Rightarrow> hterm list" where
  "thm_frees th = foldr (\<lambda>a acc. List.union (frees a) acc) (hyp th) (frees (concl th))"

text \<open>Is one term free in another?\<close>

primrec free_in_n :: "nat \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "free_in_n 0 tm1 tm2 = aconv tm1 tm2"
| "free_in_n (Suc k) tm1 tm2 =
     (if aconv tm1 tm2 then True
      else case tm2 of
        Comb l r \<Rightarrow> free_in_n k tm1 l \<or> free_in_n k tm1 r
      | Abs bv bod \<Rightarrow> \<not> vfree_in bv tm1 \<and> free_in_n k tm1 bod
      | _ \<Rightarrow> False)"

definition free_in :: "hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "free_in tm1 tm2 = free_in_n (tm_size tm2) tm1 tm2"

primrec find_terms_acc :: "nat \<Rightarrow> (hterm \<Rightarrow> bool) \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "find_terms_acc 0 p acc tm = acc"
| "find_terms_acc (Suc k) p acc tm =
     (let tl' = (if p tm then List.insert tm acc else acc) in
      case tm of
        Abs _ b \<Rightarrow> find_terms_acc k p tl' b
      | Comb l r \<Rightarrow> find_terms_acc k p (find_terms_acc k p tl' l) r
      | _ \<Rightarrow> tl')"

definition find_terms :: "(hterm \<Rightarrow> bool) \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "find_terms p tm = find_terms_acc (tm_size tm) p [] tm"

section \<open>Printing\<close>

fun sep_by :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "sep_by sep [] = []"
| "sep_by sep [x] = x"
| "sep_by sep (x # xs) = x @ sep @ sep_by sep xs"

primrec pp_ty :: "hol_type \<Rightarrow> string" where
  "pp_ty (Tyvar v) = ''?'' @ v"
| "pp_ty (Tyapp c args) =
     (let ps = map pp_ty args in
      if c = ''fun'' \<and> length ps = 2 then ''('' @ ps ! 0 @ ''->'' @ ps ! 1 @ '')''
      else if ps = [] then c
      else c @ ''<'' @ sep_by '','' ps @ ''>'')"

definition pp_op :: "string \<Rightarrow> string option" where
  "pp_op c = (if c = ''='' then Some ''='' else if c = ''AND'' then Some ''&''
              else if c = ''OR'' then Some ''|'' else if c = ''IMP'' then Some ''==>'' else None)"

fun pp_tm :: "hterm \<Rightarrow> string" where
  "pp_tm (Var n _) = n"
| "pp_tm (Const n _) = n"
| "pp_tm (Comb (Comb (Const c _) a) b) =
     (case pp_op c of
        Some o' \<Rightarrow> ''('' @ pp_tm a @ '' '' @ o' @ '' '' @ pp_tm b @ '')''
      | None \<Rightarrow> ''('' @ c @ '' '' @ pp_tm a @ '' '' @ pp_tm b @ '')'')"
| "pp_tm (Comb (Const c _) (Abs v b)) =
     (if c = ''ALL'' then ''!'' @ pp_tm v @ ''. '' @ pp_tm b
      else if c = ''EX'' then ''?'' @ pp_tm v @ ''. '' @ pp_tm b
      else ''('' @ c @ '' (fn '' @ pp_tm v @ ''. '' @ pp_tm b @ ''))'')"
| "pp_tm (Comb (Const c _) a) = (if c = ''NOT'' then ''~'' @ pp_tm a else ''('' @ c @ '' '' @ pp_tm a @ '')'')"
| "pp_tm (Comb s t) = ''('' @ pp_tm s @ '' '' @ pp_tm t @ '')''"
| "pp_tm (Abs v b) = ''(fn '' @ pp_tm v @ ''. '' @ pp_tm b @ '')''"

definition pp_thm :: "hthm \<Rightarrow> string" where
  "pp_thm th = sep_by '', '' (map pp_tm (hyp th)) @ '' |- '' @ pp_tm (concl th)"

section \<open>Basic equality reasoning and conversionals (equal.ml)\<close>

definition AP_TERM :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "AP_TERM tm th = MK_COMB (REFL tm) th"

definition AP_THM :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "AP_THM th tm = MK_COMB th (REFL tm)"

definition SYM :: "hthm \<Rightarrow> hthm option" where
  "SYM th =
     (let tm = concl th in
      do { (l, _) \<leftarrow> dest_eq tm;
           eqc \<leftarrow> Option.bind (rator tm) rator;
           let lth = REFL l;
           t1 \<leftarrow> AP_TERM eqc th;
           t2 \<leftarrow> MK_COMB t1 lth;
           EQ_MP t2 lth })"

definition ALPHA :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "ALPHA tm1 tm2 = TRANS (REFL tm1) (REFL tm2)"

definition ALPHA_CONV :: "hterm \<Rightarrow> conv" where
  "ALPHA_CONV v tm = do { res \<leftarrow> alpha v tm; ALPHA tm res }"

definition GEN_ALPHA_CONV :: "hterm \<Rightarrow> conv" where
  "GEN_ALPHA_CONV v tm =
     (case tm of
        Abs _ _ \<Rightarrow> ALPHA_CONV v tm
      | Comb b ab \<Rightarrow> do { th \<leftarrow> ALPHA_CONV v ab; AP_TERM b th }
      | _ \<Rightarrow> None)"

definition MK_BINOP :: "hterm \<Rightarrow> hthm \<times> hthm \<Rightarrow> hthm option" where
  "MK_BINOP opr p = do { a \<leftarrow> AP_TERM opr (fst p); MK_COMB a (snd p) }"

definition NO_CONV :: conv where "NO_CONV tm = None"

definition ALL_CONV :: conv where "ALL_CONV tm = Some (REFL tm)"

definition THENC :: "conv \<Rightarrow> conv \<Rightarrow> conv" where
  "THENC conv1 conv2 t =
     do { th1 \<leftarrow> conv1 t; r \<leftarrow> rand (concl th1); th2 \<leftarrow> conv2 r; TRANS th1 th2 }"

definition ORELSEC :: "conv \<Rightarrow> conv \<Rightarrow> conv" where
  "ORELSEC conv1 conv2 t = (case conv1 t of Some th \<Rightarrow> Some th | None \<Rightarrow> conv2 t)"

fun FIRST_CONV :: "conv list \<Rightarrow> conv" where
  "FIRST_CONV [] = NO_CONV"
| "FIRST_CONV [c] = c"
| "FIRST_CONV (c # cs) = ORELSEC c (FIRST_CONV cs)"

definition EVERY_CONV :: "conv list \<Rightarrow> conv" where
  "EVERY_CONV l = foldr THENC l ALL_CONV"

text \<open>@{text REPEATC} loops until the conversion fails; it is a partial function.\<close>

partial_function (option) repeatc :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "repeatc conv t =
     (case conv t of
        None \<Rightarrow> Some (Some (REFL t))
      | Some th1 \<Rightarrow>
          (case rand (concl th1) of
             None \<Rightarrow> Some (Some (REFL t))
           | Some r \<Rightarrow>
               do { r2 \<leftarrow> repeatc conv r;
                    (case r2 of
                       Some th2 \<Rightarrow> (case TRANS th1 th2 of Some th \<Rightarrow> Some (Some th) | None \<Rightarrow> Some (Some (REFL t)))
                     | None \<Rightarrow> Some (Some (REFL t))) }))"

declare repeatc.simps [code]

definition REPEATC :: "conv \<Rightarrow> conv" where
  "REPEATC conv t = (case repeatc conv t of Some r \<Rightarrow> r | None \<Rightarrow> None)"

definition CHANGED_CONV :: "conv \<Rightarrow> conv" where
  "CHANGED_CONV conv tm =
     do { th \<leftarrow> conv tm; (l, r) \<leftarrow> dest_eq (concl th); (if aconv l r then None else Some th) }"

definition TRY_CONV :: "conv \<Rightarrow> conv" where
  "TRY_CONV conv = ORELSEC conv ALL_CONV"

definition RATOR_CONV :: "conv \<Rightarrow> conv" where
  "RATOR_CONV conv tm = (case tm of Comb l r \<Rightarrow> do { th \<leftarrow> conv l; AP_THM th r } | _ \<Rightarrow> None)"

definition RAND_CONV :: "conv \<Rightarrow> conv" where
  "RAND_CONV conv tm = (case tm of Comb l r \<Rightarrow> do { th \<leftarrow> conv r; MK_COMB (REFL l) th } | _ \<Rightarrow> None)"

definition LAND_CONV :: "conv \<Rightarrow> conv" where
  "LAND_CONV conv = RATOR_CONV (RAND_CONV conv)"

definition COMB2_CONV :: "conv \<Rightarrow> conv \<Rightarrow> conv" where
  "COMB2_CONV lconv rconv tm =
     (case tm of Comb l r \<Rightarrow> do { a \<leftarrow> lconv l; b \<leftarrow> rconv r; MK_COMB a b } | _ \<Rightarrow> None)"

definition COMB_CONV :: "conv \<Rightarrow> conv" where
  "COMB_CONV conv = COMB2_CONV conv conv"

definition abs_fallback :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "abs_fallback v gv gth0 =
     do { gth \<leftarrow> ABS gv gth0;
          let gtm = concl gth;
          (l, r) \<leftarrow> dest_eq gtm;
          let v' = variant (frees gtm) v;
          l' \<leftarrow> alpha v' l;
          r' \<leftarrow> alpha v' r;
          eq \<leftarrow> mk_eq l' r';
          al \<leftarrow> ALPHA gtm eq;
          EQ_MP al gth }"

definition ABS_CONV :: "conv \<Rightarrow> conv" where
  "ABS_CONV conv tm =
     (case tm of
        Abs v bod \<Rightarrow>
          do { th \<leftarrow> conv bod;
               (case ABS v th of
                  Some r \<Rightarrow> Some r
                | None \<Rightarrow>
                    (let gv = genvar [tm] (type_of v);
                         gbod = vsubst [(gv, v)] bod
                     in do { gth0 \<leftarrow> conv gbod; abs_fallback v gv gth0 })) }
      | _ \<Rightarrow> None)"

definition BINDER_CONV :: "conv \<Rightarrow> conv" where
  "BINDER_CONV conv tm = (case tm of Abs _ _ \<Rightarrow> ABS_CONV conv tm | _ \<Rightarrow> RAND_CONV (ABS_CONV conv) tm)"

definition SUB_CONV :: "conv \<Rightarrow> conv" where
  "SUB_CONV conv tm =
     (case tm of Comb _ _ \<Rightarrow> COMB_CONV conv tm | Abs _ _ \<Rightarrow> ABS_CONV conv tm | _ \<Rightarrow> Some (REFL tm))"

definition BINOP_CONV :: "conv \<Rightarrow> conv" where
  "BINOP_CONV conv tm =
     do { (lop, r) \<leftarrow> dest_comb tm; (opr, l) \<leftarrow> dest_comb lop;
          a \<leftarrow> conv l; b \<leftarrow> conv r; c \<leftarrow> AP_TERM opr a; MK_COMB c b }"

definition BINOP2_CONV :: "conv \<Rightarrow> conv \<Rightarrow> conv" where
  "BINOP2_CONV conv1 conv2 tm =
     do { (lop, r) \<leftarrow> dest_comb tm; (opr, l) \<leftarrow> dest_comb lop;
          a \<leftarrow> conv1 l; b \<leftarrow> conv2 r; c \<leftarrow> AP_TERM opr a; MK_COMB c b }"

text \<open>Depth conversions.  HOL Light uses a failure-propagating ("Boultonized") version to avoid
  rebuilding terms.  The quasi-conversions are partial functions into @{typ "hthm option option"}:
  @{text "Some None"} is an OCaml failure and @{text None} non-termination.  Each is
  self-recursive, with @{text SUB_QCONV} written out in each of them.\<close>

partial_function (option) repeatqc :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "repeatqc conv tm =
     (case conv tm of
        None \<Rightarrow> Some None
      | Some th1 \<Rightarrow>
          (case rand (concl th1) of
             None \<Rightarrow> Some None
           | Some r \<Rightarrow>
               do { b \<leftarrow> repeatqc conv r;
                    (case b of Some th2 \<Rightarrow> Some (TRANS th1 th2) | None \<Rightarrow> Some (Some th1)) }))"

declare repeatqc.simps [code]

partial_function (option) once_depth_qconv :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "once_depth_qconv conv tm =
     (case conv tm of
        Some th \<Rightarrow> Some (Some th)
      | None \<Rightarrow>
          (case tm of
             Abs v bod \<Rightarrow>
               do { x \<leftarrow> once_depth_qconv conv bod;
                    (case x of
                       None \<Rightarrow> Some None
                     | Some th \<Rightarrow>
                         (case ABS v th of
                            Some y \<Rightarrow> Some (Some y)
                          | None \<Rightarrow>
                              do { y \<leftarrow> once_depth_qconv conv (vsubst [(genvar [tm] (type_of v), v)] bod);
                                   (case y of
                                      None \<Rightarrow> Some None
                                    | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [tm] (type_of v)) gth0)) })) }
           | Comb l r' \<Rightarrow>
               do { a \<leftarrow> once_depth_qconv conv l;
                    (case a of
                       Some th1 \<Rightarrow>
                         do { b \<leftarrow> once_depth_qconv conv r';
                              (case b of
                                 Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                               | None \<Rightarrow> Some (AP_THM th1 r')) }
                     | None \<Rightarrow>
                         do { b \<leftarrow> once_depth_qconv conv r';
                              (case b of
                                 Some th2 \<Rightarrow> Some (AP_TERM l th2)
                               | None \<Rightarrow> Some None) }) }
           | _ \<Rightarrow> Some None))"

declare once_depth_qconv.simps [code]

partial_function (option) depth_qconv :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "depth_qconv conv tm =
     do { a \<leftarrow> (case tm of
            Abs v bod \<Rightarrow>
              do { x \<leftarrow> depth_qconv conv bod;
                   (case x of
                      None \<Rightarrow> Some None
                    | Some th \<Rightarrow>
                        (case ABS v th of
                           Some y \<Rightarrow> Some (Some y)
                         | None \<Rightarrow>
                             do { y \<leftarrow> depth_qconv conv (vsubst [(genvar [tm] (type_of v), v)] bod);
                                  (case y of
                                     None \<Rightarrow> Some None
                                   | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [tm] (type_of v)) gth0)) })) }
          | Comb l r' \<Rightarrow>
              do { a \<leftarrow> depth_qconv conv l;
                   (case a of
                      Some th1 \<Rightarrow>
                        do { b \<leftarrow> depth_qconv conv r';
                             (case b of
                                Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                              | None \<Rightarrow> Some (AP_THM th1 r')) }
                    | None \<Rightarrow>
                        do { b \<leftarrow> depth_qconv conv r';
                             (case b of
                                Some th2 \<Rightarrow> Some (AP_TERM l th2)
                              | None \<Rightarrow> Some None) }) }
          | _ \<Rightarrow> Some None);
          (case a of
             Some th1 \<Rightarrow>
               (case rand (concl th1) of
                  None \<Rightarrow> Some None
                | Some r \<Rightarrow>
                    do { b \<leftarrow> repeatqc conv r;
                         (case b of Some th2 \<Rightarrow> Some (TRANS th1 th2) | None \<Rightarrow> Some (Some th1)) })
           | None \<Rightarrow> repeatqc conv tm) }"

declare depth_qconv.simps [code]

partial_function (option) redepth_qconv :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "redepth_qconv conv tm =
     do { a \<leftarrow> (case tm of
            Abs v bod \<Rightarrow>
              do { x \<leftarrow> redepth_qconv conv bod;
                   (case x of
                      None \<Rightarrow> Some None
                    | Some th \<Rightarrow>
                        (case ABS v th of
                           Some y \<Rightarrow> Some (Some y)
                         | None \<Rightarrow>
                             do { y \<leftarrow> redepth_qconv conv (vsubst [(genvar [tm] (type_of v), v)] bod);
                                  (case y of
                                     None \<Rightarrow> Some None
                                   | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [tm] (type_of v)) gth0)) })) }
          | Comb l r' \<Rightarrow>
              do { a \<leftarrow> redepth_qconv conv l;
                   (case a of
                      Some th1 \<Rightarrow>
                        do { b \<leftarrow> redepth_qconv conv r';
                             (case b of
                                Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                              | None \<Rightarrow> Some (AP_THM th1 r')) }
                    | None \<Rightarrow>
                        do { b \<leftarrow> redepth_qconv conv r';
                             (case b of
                                Some th2 \<Rightarrow> Some (AP_TERM l th2)
                              | None \<Rightarrow> Some None) }) }
          | _ \<Rightarrow> Some None);
          (case a of
             Some th1 \<Rightarrow>
               (case rand (concl th1) of
                  None \<Rightarrow> Some None
                | Some r \<Rightarrow>
                    do { c \<leftarrow> (case conv r of
                                None \<Rightarrow> Some None
                              | Some t1 \<Rightarrow>
                                  (case rand (concl t1) of
                                     None \<Rightarrow> Some None
                                   | Some r2 \<Rightarrow>
                                       do { b \<leftarrow> redepth_qconv conv r2;
                                            (case b of
                                               Some t2 \<Rightarrow> Some (TRANS t1 t2)
                                             | None \<Rightarrow> Some (Some t1)) }));
                         (case c of Some th2 \<Rightarrow> Some (TRANS th1 th2) | None \<Rightarrow> Some (Some th1)) })
           | None \<Rightarrow>
               (case conv tm of
                  None \<Rightarrow> Some None
                | Some t1 \<Rightarrow>
                    (case rand (concl t1) of
                       None \<Rightarrow> Some None
                     | Some r2 \<Rightarrow>
                         do { b \<leftarrow> redepth_qconv conv r2;
                              (case b of
                                 Some t2 \<Rightarrow> Some (TRANS t1 t2)
                               | None \<Rightarrow> Some (Some t1)) }))) }"

declare redepth_qconv.simps [code]

partial_function (option) top_depth_qconv :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "top_depth_qconv conv tm =
     do { a \<leftarrow> repeatqc conv tm;
          (case a of
             Some th1 \<Rightarrow>
               (case rand (concl th1) of
                  None \<Rightarrow> Some None
                | Some r \<Rightarrow>
                    do { c \<leftarrow> do { x \<leftarrow> (case r of
                         Abs v bod \<Rightarrow>
                           do { x \<leftarrow> top_depth_qconv conv bod;
                                (case x of
                                   None \<Rightarrow> Some None
                                 | Some th \<Rightarrow>
                                     (case ABS v th of
                                        Some y \<Rightarrow> Some (Some y)
                                      | None \<Rightarrow>
                                          do { y \<leftarrow> top_depth_qconv conv (vsubst [(genvar [r] (type_of v), v)] bod);
                                               (case y of
                                                  None \<Rightarrow> Some None
                                                | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [r] (type_of v)) gth0)) })) }
                       | Comb l r' \<Rightarrow>
                           do { a \<leftarrow> top_depth_qconv conv l;
                                (case a of
                                   Some th1 \<Rightarrow>
                                     do { b \<leftarrow> top_depth_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                                           | None \<Rightarrow> Some (AP_THM th1 r')) }
                                 | None \<Rightarrow>
                                     do { b \<leftarrow> top_depth_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (AP_TERM l th2)
                                           | None \<Rightarrow> Some None) }) }
                       | _ \<Rightarrow> Some None);
                                  (case x of
                                     None \<Rightarrow> Some None
                                   | Some s1 \<Rightarrow>
                                       (case rand (concl s1) of
                                          None \<Rightarrow> Some None
                                        | Some r' \<Rightarrow>
                                            do { y \<leftarrow> (case conv r' of
                                                        None \<Rightarrow> Some None
                                                      | Some t1 \<Rightarrow>
                                                          (case rand (concl t1) of
                                                             None \<Rightarrow> Some None
                                                           | Some r2 \<Rightarrow>
                                                               do { b \<leftarrow> top_depth_qconv conv r2;
                                                                    (case b of
                                                                       Some t2 \<Rightarrow> Some (TRANS t1 t2)
                                                                     | None \<Rightarrow> Some (Some t1)) }));
                                                 (case y of
                                                    Some s2 \<Rightarrow> Some (TRANS s1 s2)
                                                  | None \<Rightarrow> Some (Some s1)) })) };
                         (case c of Some th2 \<Rightarrow> Some (TRANS th1 th2) | None \<Rightarrow> Some (Some th1)) })
           | None \<Rightarrow>
               do { x \<leftarrow> (case tm of
                         Abs v bod \<Rightarrow>
                           do { x \<leftarrow> top_depth_qconv conv bod;
                                (case x of
                                   None \<Rightarrow> Some None
                                 | Some th \<Rightarrow>
                                     (case ABS v th of
                                        Some y \<Rightarrow> Some (Some y)
                                      | None \<Rightarrow>
                                          do { y \<leftarrow> top_depth_qconv conv (vsubst [(genvar [tm] (type_of v), v)] bod);
                                               (case y of
                                                  None \<Rightarrow> Some None
                                                | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [tm] (type_of v)) gth0)) })) }
                       | Comb l r' \<Rightarrow>
                           do { a \<leftarrow> top_depth_qconv conv l;
                                (case a of
                                   Some th1 \<Rightarrow>
                                     do { b \<leftarrow> top_depth_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                                           | None \<Rightarrow> Some (AP_THM th1 r')) }
                                 | None \<Rightarrow>
                                     do { b \<leftarrow> top_depth_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (AP_TERM l th2)
                                           | None \<Rightarrow> Some None) }) }
                       | _ \<Rightarrow> Some None);
                    (case x of
                       None \<Rightarrow> Some None
                     | Some s1 \<Rightarrow>
                         (case rand (concl s1) of
                            None \<Rightarrow> Some None
                          | Some r' \<Rightarrow>
                              do { y \<leftarrow> (case conv r' of
                                          None \<Rightarrow> Some None
                                        | Some t1 \<Rightarrow>
                                            (case rand (concl t1) of
                                               None \<Rightarrow> Some None
                                             | Some r2 \<Rightarrow>
                                                 do { b \<leftarrow> top_depth_qconv conv r2;
                                                      (case b of
                                                         Some t2 \<Rightarrow> Some (TRANS t1 t2)
                                                       | None \<Rightarrow> Some (Some t1)) }));
                                   (case y of
                                      Some s2 \<Rightarrow> Some (TRANS s1 s2)
                                    | None \<Rightarrow> Some (Some s1)) })) }) }"

declare top_depth_qconv.simps [code]

partial_function (option) top_sweep_qconv :: "conv \<Rightarrow> hterm \<Rightarrow> hthm option option" where
  "top_sweep_qconv conv tm =
     do { a \<leftarrow> repeatqc conv tm;
          (case a of
             Some th1 \<Rightarrow>
               (case rand (concl th1) of
                  None \<Rightarrow> Some None
                | Some r \<Rightarrow>
                    do { b \<leftarrow> (case r of
                         Abs v bod \<Rightarrow>
                           do { x \<leftarrow> top_sweep_qconv conv bod;
                                (case x of
                                   None \<Rightarrow> Some None
                                 | Some th \<Rightarrow>
                                     (case ABS v th of
                                        Some y \<Rightarrow> Some (Some y)
                                      | None \<Rightarrow>
                                          do { y \<leftarrow> top_sweep_qconv conv (vsubst [(genvar [r] (type_of v), v)] bod);
                                               (case y of
                                                  None \<Rightarrow> Some None
                                                | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [r] (type_of v)) gth0)) })) }
                       | Comb l r' \<Rightarrow>
                           do { a \<leftarrow> top_sweep_qconv conv l;
                                (case a of
                                   Some th1 \<Rightarrow>
                                     do { b \<leftarrow> top_sweep_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                                           | None \<Rightarrow> Some (AP_THM th1 r')) }
                                 | None \<Rightarrow>
                                     do { b \<leftarrow> top_sweep_qconv conv r';
                                          (case b of
                                             Some th2 \<Rightarrow> Some (AP_TERM l th2)
                                           | None \<Rightarrow> Some None) }) }
                       | _ \<Rightarrow> Some None);
                         (case b of Some th2 \<Rightarrow> Some (TRANS th1 th2) | None \<Rightarrow> Some (Some th1)) })
           | None \<Rightarrow> (case tm of
                   Abs v bod \<Rightarrow>
                     do { x \<leftarrow> top_sweep_qconv conv bod;
                          (case x of
                             None \<Rightarrow> Some None
                           | Some th \<Rightarrow>
                               (case ABS v th of
                                  Some y \<Rightarrow> Some (Some y)
                                | None \<Rightarrow>
                                    do { y \<leftarrow> top_sweep_qconv conv (vsubst [(genvar [tm] (type_of v), v)] bod);
                                         (case y of
                                            None \<Rightarrow> Some None
                                          | Some gth0 \<Rightarrow> Some (abs_fallback v (genvar [tm] (type_of v)) gth0)) })) }
                 | Comb l r' \<Rightarrow>
                     do { a \<leftarrow> top_sweep_qconv conv l;
                          (case a of
                             Some th1 \<Rightarrow>
                               do { b \<leftarrow> top_sweep_qconv conv r';
                                    (case b of
                                       Some th2 \<Rightarrow> Some (MK_COMB th1 th2)
                                     | None \<Rightarrow> Some (AP_THM th1 r')) }
                           | None \<Rightarrow>
                               do { b \<leftarrow> top_sweep_qconv conv r';
                                    (case b of
                                       Some th2 \<Rightarrow> Some (AP_TERM l th2)
                                     | None \<Rightarrow> Some None) }) }
                 | _ \<Rightarrow> Some None)) }"

declare top_sweep_qconv.simps [code]

definition ONCE_DEPTH_CONV :: "conv \<Rightarrow> conv" where
  "ONCE_DEPTH_CONV c = TRY_CONV (\<lambda>tm. case once_depth_qconv c tm of Some r \<Rightarrow> r | None \<Rightarrow> None)"
definition DEPTH_CONV :: "conv \<Rightarrow> conv" where
  "DEPTH_CONV c = TRY_CONV (\<lambda>tm. case depth_qconv c tm of Some r \<Rightarrow> r | None \<Rightarrow> None)"
definition REDEPTH_CONV :: "conv \<Rightarrow> conv" where
  "REDEPTH_CONV c = TRY_CONV (\<lambda>tm. case redepth_qconv c tm of Some r \<Rightarrow> r | None \<Rightarrow> None)"
definition TOP_DEPTH_CONV :: "conv \<Rightarrow> conv" where
  "TOP_DEPTH_CONV c = TRY_CONV (\<lambda>tm. case top_depth_qconv c tm of Some r \<Rightarrow> r | None \<Rightarrow> None)"
definition TOP_SWEEP_CONV :: "conv \<Rightarrow> conv" where
  "TOP_SWEEP_CONV c = TRY_CONV (\<lambda>tm. case top_sweep_qconv c tm of Some r \<Rightarrow> r | None \<Rightarrow> None)"


text \<open>@{text BETA_CONV} and @{text CONV_RULE}.\<close>

definition BETA_CONV :: conv where
  "BETA_CONV tm =
     (case BETA tm of
        Some th \<Rightarrow> Some th
      | None \<Rightarrow>
          do { (f, arg) \<leftarrow> dest_comb tm;
               v \<leftarrow> bndvar f;
               fv \<leftarrow> mk_comb f v;
               th1 \<leftarrow> BETA fv;
               INST [(arg, v)] th1 })"

definition CONV_RULE :: "conv \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONV_RULE conv th = do { e \<leftarrow> conv (concl th); EQ_MP e th }"

definition SYM_CONV :: conv where
  "SYM_CONV tm =
     do { th1 \<leftarrow> (do { a \<leftarrow> ASSUME tm; SYM a });
          let tm' = concl th1;
          th2 \<leftarrow> (do { a \<leftarrow> ASSUME tm'; SYM a });
          Some (DEDUCT_ANTISYM_RULE th2 th1) }"

definition BETA_RULE :: "hthm \<Rightarrow> hthm option" where
  "BETA_RULE = CONV_RULE (REDEPTH_CONV BETA_CONV)"

definition GSYM :: "hthm \<Rightarrow> hthm option" where
  "GSYM = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)"

definition SUBS_CONV :: "hthm list \<Rightarrow> conv" where
  "SUBS_CONV ths tm =
     (if ths = [] then Some (REFL tm)
      else
        do { lefts \<leftarrow> those (map (\<lambda>th. lhand (concl th)) ths);
             let gvs = snd (foldl (\<lambda>(av, acc) x. (let g = genvar (av @ [tm]) (type_of x) in (av @ [g], acc @ [g]))) ([], []) lefts);
             pat \<leftarrow> subst (zip gvs lefts) tm;
             abs' \<leftarrow> list_mk_abs gvs pat;
             th \<leftarrow> foldr (\<lambda>y acc. do { x \<leftarrow> acc;
                                      mk \<leftarrow> MK_COMB x y;
                                      CONV_RULE (THENC (RAND_CONV BETA_CONV) (LAND_CONV BETA_CONV)) mk })
                        (rev ths) (Some (REFL abs'));
             r \<leftarrow> rand (concl th);
             (if r = tm then Some (REFL tm) else Some th) })"

definition SUBS :: "hthm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SUBS ths = CONV_RULE (SUBS_CONV ths)"

section \<open>The logical constants (bool.ml)\<close>

definition T_tm :: hterm where "T_tm = Const ''T'' bool_ty"
definition F_tm :: hterm where "F_tm = Const ''F'' bool_ty"
definition and_c :: hterm where "and_c = Const ''AND'' bbb_ty"
definition imp_c :: hterm where "imp_c = Const ''IMP'' bbb_ty"
definition or_c :: hterm where "or_c = Const ''OR'' bbb_ty"
definition not_c :: hterm where "not_c = Const ''NOT'' bb_ty"
definition forall_c :: "hol_type \<Rightarrow> hterm" where
  "forall_c ty = Const ''ALL'' (fun_ty (fun_ty ty bool_ty) bool_ty)"
definition exists_c :: "hol_type \<Rightarrow> hterm" where
  "exists_c ty = Const ''EX'' (fun_ty (fun_ty ty bool_ty) bool_ty)"
definition uexists_c :: "hol_type \<Rightarrow> hterm" where
  "uexists_c ty = Const ''EXU'' (fun_ty (fun_ty ty bool_ty) bool_ty)"

definition mk_neg :: "hterm \<Rightarrow> hterm" where "mk_neg p = Comb not_c p"
definition mk_not :: "hterm \<Rightarrow> hterm" where "mk_not = mk_neg"
definition mk_conj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_conj p q = Comb (Comb and_c p) q"
definition mk_disj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_disj p q = Comb (Comb or_c p) q"
definition mk_imp :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_imp p q = Comb (Comb imp_c p) q"
definition mk_iff :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_iff = safe_mk_eq"

definition mk_forall :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_forall v bod = (case v of Var _ ty \<Rightarrow> Comb (forall_c ty) (Abs v bod) | _ \<Rightarrow> bod)"
definition mk_exists :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_exists v bod = (case v of Var _ ty \<Rightarrow> Comb (exists_c ty) (Abs v bod) | _ \<Rightarrow> bod)"
definition mk_uexists :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_uexists v bod = (case v of Var _ ty \<Rightarrow> Comb (uexists_c ty) (Abs v bod) | _ \<Rightarrow> bod)"

definition mk_foralls :: "hterm list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_foralls vs bd = foldr mk_forall vs bd"

definition dest_conj :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_conj = dest_binary ''AND''"
definition dest_disj :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_disj = dest_binary ''OR''"
definition dest_imp :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_imp = dest_binary ''IMP''"
definition is_conj :: "hterm \<Rightarrow> bool" where "is_conj tm = (dest_conj tm \<noteq> None)"
definition is_imp :: "hterm \<Rightarrow> bool" where "is_imp tm = (dest_imp tm \<noteq> None)"

fun dest_neg :: "hterm \<Rightarrow> hterm option" where
  "dest_neg (Comb (Const n _) p) = (if n = ''NOT'' then Some p else None)"
| "dest_neg _ = None"

definition is_neg :: "hterm \<Rightarrow> bool" where "is_neg tm = (dest_neg tm \<noteq> None)"

definition dest_forall :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_forall = dest_binder ''ALL''"
definition dest_exists :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_exists = dest_binder ''EX''"
definition is_forall :: "hterm \<Rightarrow> bool" where "is_forall tm = (dest_forall tm \<noteq> None)"

fun is_iff :: "hterm \<Rightarrow> bool" where
  "is_iff (Comb (Comb (Const n (Tyapp f (Tyapp b [] # _))) _) _) = (n = ''='' \<and> f = ''fun'' \<and> b = ''bool'')"
| "is_iff _ = False"

definition dest_iff :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_iff tm = (if is_iff tm then dest_eq tm else None)"

text \<open>Variables used in proforma theorems.\<close>

definition vp :: hterm where "vp = Var ''p'' bool_ty"
definition vq :: hterm where "vq = Var ''q'' bool_ty"
definition vr :: hterm where "vr = Var ''r'' bool_ty"
definition vt :: hterm where "vt = Var ''t'' bool_ty"
definition vf :: hterm where "vf = Var ''f'' bbb_ty"
definition vPb :: hterm where "vPb = Var ''P'' bool_ty"
definition vQb :: hterm where "vQb = Var ''Q'' bool_ty"
definition vRb :: hterm where "vRb = Var ''R'' bool_ty"
definition vPA :: hterm where "vPA = Var ''P'' (fun_ty aty bool_ty)"
definition vx :: hterm where "vx = Var ''x'' aty"
definition vy :: hterm where "vy = Var ''y'' aty"

definition all_ty :: hol_type where "all_ty = fun_ty (fun_ty aty bool_ty) bool_ty"

definition mk_defn :: "string \<Rightarrow> hol_type \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_defn name ty r = safe_mk_eq (Var name ty) r"

definition t_def_tm :: hterm where
  "t_def_tm = mk_defn ''T'' bool_ty (safe_mk_eq (Abs vp vp) (Abs vp vp))"

definition and_def_tm :: hterm where
  "and_def_tm = mk_defn ''AND'' bbb_ty
     (Abs vp (Abs vq (safe_mk_eq (Abs vf (Comb (Comb vf vp) vq)) (Abs vf (Comb (Comb vf T_tm) T_tm)))))"

definition imp_def_tm :: hterm where
  "imp_def_tm = mk_defn ''IMP'' bbb_ty (Abs vp (Abs vq (mk_iff (mk_conj vp vq) vp)))"

definition forall_def_tm :: hterm where
  "forall_def_tm = mk_defn ''ALL'' all_ty (Abs vPA (safe_mk_eq vPA (Abs vx T_tm)))"

definition exists_def_tm :: hterm where
  "exists_def_tm = mk_defn ''EX'' all_ty
     (Abs vPA (mk_forall vq (mk_imp (mk_forall vx (mk_imp (Comb vPA vx) vq)) vq)))"

definition or_def_tm :: hterm where
  "or_def_tm = mk_defn ''OR'' bbb_ty
     (Abs vp (Abs vq (mk_forall vr (mk_imp (mk_imp vp vr) (mk_imp (mk_imp vq vr) vr)))))"

definition f_def_tm :: hterm where
  "f_def_tm = mk_defn ''F'' bool_ty (mk_forall vp vp)"

definition not_def_tm :: hterm where
  "not_def_tm = mk_defn ''NOT'' bb_ty (Abs vp (mk_imp vp F_tm))"

definition exists_unique_def_tm :: hterm where
  "exists_unique_def_tm = mk_defn ''EXU'' all_ty
     (Abs vPA (mk_conj (Comb (exists_c aty) vPA)
                       (mk_forall vx (mk_forall vy (mk_imp (mk_conj (Comb vPA vx) (Comb vPA vy)) (safe_mk_eq vx vy))))))"

definition bool_cases_tm :: hterm where
  "bool_cases_tm = mk_forall vt (mk_disj (mk_iff vt T_tm) (mk_iff vt F_tm))"

text \<open>The definitions are run through the kernel; @{text BOOL_CASES_AX} is the one axiom.\<close>

definition bool_init :: "(kstate \<times> hthm list) option" where
  "bool_init =
     do { (k1, t1) \<leftarrow> new_basic_definition init_kstate t_def_tm;
          (k2, t2) \<leftarrow> new_basic_definition k1 and_def_tm;
          (k3, t3) \<leftarrow> new_basic_definition k2 imp_def_tm;
          (k4, t4) \<leftarrow> new_basic_definition k3 forall_def_tm;
          (k5, t5) \<leftarrow> new_basic_definition k4 exists_def_tm;
          (k6, t6) \<leftarrow> new_basic_definition k5 or_def_tm;
          (k7, t7) \<leftarrow> new_basic_definition k6 f_def_tm;
          (k8, t8) \<leftarrow> new_basic_definition k7 not_def_tm;
          (k9, t9) \<leftarrow> new_basic_definition k8 exists_unique_def_tm;
          (k10, t10) \<leftarrow> new_axiom k9 bool_cases_tm;
          Some (k10, [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]) }"

definition bool_kstate :: kstate where "bool_kstate = fst (the bool_init)"

definition bthm :: "nat \<Rightarrow> hthm" where "bthm i = (snd (the bool_init)) ! i"

definition T_DEF :: hthm where "T_DEF = bthm 0"
definition AND_DEF :: hthm where "AND_DEF = bthm 1"
definition IMP_DEF :: hthm where "IMP_DEF = bthm 2"
definition FORALL_DEF :: hthm where "FORALL_DEF = bthm 3"
definition EXISTS_DEF :: hthm where "EXISTS_DEF = bthm 4"
definition OR_DEF :: hthm where "OR_DEF = bthm 5"
definition F_DEF :: hthm where "F_DEF = bthm 6"
definition NOT_DEF :: hthm where "NOT_DEF = bthm 7"
definition EXISTS_UNIQUE_DEF :: hthm where "EXISTS_UNIQUE_DEF = bthm 8"
definition BOOL_CASES_AX :: hthm where "BOOL_CASES_AX = bthm 9"


section \<open>Derived rules (bool.ml)\<close>

text \<open>Rule allowing easy instantiation of polymorphic proformas.\<close>

definition PINST :: "(hol_type \<times> hol_type) list \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "PINST tyin tmin th =
     do { tms \<leftarrow> those (map (\<lambda>p. map_option (\<lambda>x. (fst p, x)) (inst tyin (snd p))) tmin);
          th1 \<leftarrow> INST_TYPE tyin th;
          INST tms th1 }"

definition PROVE_HYP :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "PROVE_HYP ath bth =
     (if list_ex (aconv (concl ath)) (hyp bth)
      then EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
      else Some bth)"

subsection \<open>Rules for T\<close>

definition TRUTH :: hthm where
  "TRUTH = the (do { s \<leftarrow> SYM T_DEF; EQ_MP s (REFL (Abs vp vp)) })"

definition EQT_ELIM :: "hthm \<Rightarrow> hthm option" where
  "EQT_ELIM th = do { s \<leftarrow> SYM th; EQ_MP s TRUTH }"

definition EQT_INTRO_pth :: hthm where
  "EQT_INTRO_pth =
     the (do { a \<leftarrow> ASSUME vt;
               let th1 = DEDUCT_ANTISYM_RULE a TRUTH;
               b \<leftarrow> ASSUME (concl th1);
               th2 \<leftarrow> EQT_ELIM b;
               Some (DEDUCT_ANTISYM_RULE th2 th1) })"

definition EQT_INTRO :: "hthm \<Rightarrow> hthm option" where
  "EQT_INTRO th = do { i \<leftarrow> INST [(concl th, vt)] EQT_INTRO_pth; EQ_MP i th }"

subsection \<open>Rules for AND\<close>

definition and_unfold :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "and_unfold p q =
     do { a1 \<leftarrow> AP_THM AND_DEF p;
          th1 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a1;
          a2 \<leftarrow> AP_THM th1 q;
          CONV_RULE (RAND_CONV BETA_CONV) a2 }"

definition CONJ_pth :: hthm where
  "CONJ_pth =
     the (do { th2 \<leftarrow> and_unfold vp vq;
               pq \<leftarrow> ASSUME (mk_conj vp vq);
               th3 \<leftarrow> EQ_MP th2 pq;
               a3 \<leftarrow> AP_THM th3 (Abs vp (Abs vq vq));
               b3 \<leftarrow> BETA_RULE a3;
               pth1 \<leftarrow> EQT_ELIM b3;
               pth \<leftarrow> ASSUME vp;
               qth \<leftarrow> ASSUME vq;
               ep \<leftarrow> EQT_INTRO pth;
               eq' \<leftarrow> EQT_INTRO qth;
               c1 \<leftarrow> AP_TERM vf ep;
               th1' \<leftarrow> MK_COMB c1 eq';
               th2' \<leftarrow> ABS vf th1';
               ap \<leftarrow> AP_THM AND_DEF vp;
               ap2 \<leftarrow> AP_THM ap vq;
               th3' \<leftarrow> BETA_RULE ap2;
               s3 \<leftarrow> SYM th3';
               pth2 \<leftarrow> EQ_MP s3 th2';
               Some (DEDUCT_ANTISYM_RULE pth1 pth2) })"

definition CONJ :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONJ th1 th2 =
     do { th \<leftarrow> INST [(concl th1, vp), (concl th2, vq)] CONJ_pth;
          b \<leftarrow> EQ_MP (DEDUCT_ANTISYM_RULE th1 th) th1;
          EQ_MP b th2 }"

definition CONJUNCT_pth :: "bool \<Rightarrow> hthm" where
  "CONJUNCT_pth first =
     the (do { th2 \<leftarrow> and_unfold vPb vQb;
               pq \<leftarrow> ASSUME (mk_conj vPb vQb);
               th3 \<leftarrow> EQ_MP th2 pq;
               a3 \<leftarrow> AP_THM th3 (Abs vp (Abs vq (if first then vp else vq)));
               b3 \<leftarrow> BETA_RULE a3;
               EQT_ELIM b3 })"

definition CONJUNCT_gen :: "bool \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONJUNCT_gen first th =
     do { (l, r) \<leftarrow> dest_conj (concl th);
          i \<leftarrow> INST [(l, vPb), (r, vQb)] (CONJUNCT_pth first);
          EQ_MP (DEDUCT_ANTISYM_RULE th i) th }"

definition CONJUNCT1 :: "hthm \<Rightarrow> hthm option" where "CONJUNCT1 = CONJUNCT_gen True"
definition CONJUNCT2 :: "hthm \<Rightarrow> hthm option" where "CONJUNCT2 = CONJUNCT_gen False"

definition CONJ_PAIR :: "hthm \<Rightarrow> (hthm \<times> hthm) option" where
  "CONJ_PAIR th = do { a \<leftarrow> CONJUNCT1 th; b \<leftarrow> CONJUNCT2 th; Some (a, b) }"

subsection \<open>Rules for IMP\<close>

definition imp_unfold :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "imp_unfold p q = do { a \<leftarrow> AP_THM IMP_DEF p; b \<leftarrow> AP_THM a q; BETA_RULE b }"

definition MP_rth :: hthm where
  "MP_rth =
     the (do { th1 \<leftarrow> imp_unfold vp vq;
               ap \<leftarrow> ASSUME vp;
               aq \<leftarrow> ASSUME vq;
               th2 \<leftarrow> CONJ ap aq;
               apq \<leftarrow> ASSUME (mk_conj vp vq);
               th3 \<leftarrow> CONJUNCT1 apq;
               s1 \<leftarrow> SYM th1;
               pth \<leftarrow> EQ_MP s1 (DEDUCT_ANTISYM_RULE th2 th3);
               aimp \<leftarrow> ASSUME (mk_imp vp vq);
               th2' \<leftarrow> EQ_MP th1 aimp;
               s2 \<leftarrow> SYM th2';
               m \<leftarrow> EQ_MP s2 ap;
               qth \<leftarrow> CONJUNCT2 m;
               Some (DEDUCT_ANTISYM_RULE pth qth) })"

definition MP :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "MP ith th =
     do { (ant, con) \<leftarrow> dest_imp (concl ith);
          (if aconv ant (concl th)
           then do { i \<leftarrow> INST [(ant, vp), (con, vq)] MP_rth;
                     b \<leftarrow> EQ_MP (DEDUCT_ANTISYM_RULE th i) th;
                     EQ_MP b ith }
           else None) }"

definition DISCH_pth :: hthm where
  "DISCH_pth = the (do { th1 \<leftarrow> imp_unfold vp vq; SYM th1 })"

definition DISCH :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISCH a th =
     do { a1 \<leftarrow> ASSUME a;
          th1 \<leftarrow> CONJ a1 th;
          ac \<leftarrow> ASSUME (concl th1);
          th2 \<leftarrow> CONJUNCT1 ac;
          let th3 = DEDUCT_ANTISYM_RULE th1 th2;
          th4 \<leftarrow> INST [(a, vp), (concl th, vq)] DISCH_pth;
          EQ_MP th4 th3 }"

primrec DISCH_ALL_n :: "nat \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISCH_ALL_n 0 th = Some th"
| "DISCH_ALL_n (Suc n) th =
     (case hyp th of
        [] \<Rightarrow> Some th
      | h # _ \<Rightarrow> (case DISCH h th of Some th' \<Rightarrow> DISCH_ALL_n n th' | None \<Rightarrow> Some th))"

definition DISCH_ALL :: "hthm \<Rightarrow> hthm option" where
  "DISCH_ALL th = DISCH_ALL_n (length (hyp th) + 1) th"

definition UNDISCH :: "hthm \<Rightarrow> hthm option" where
  "UNDISCH th = do { a \<leftarrow> rator (concl th); b \<leftarrow> rand a; ab \<leftarrow> ASSUME b; MP th ab }"

primrec UNDISCH_ALL_n :: "nat \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "UNDISCH_ALL_n 0 th = Some th"
| "UNDISCH_ALL_n (Suc n) th =
     (if is_imp (concl th) then do { th' \<leftarrow> UNDISCH th; UNDISCH_ALL_n n th' } else Some th)"

definition UNDISCH_ALL :: "hthm \<Rightarrow> hthm option" where
  "UNDISCH_ALL th = UNDISCH_ALL_n (tm_size (concl th)) th"

definition IMP_ANTISYM_pth :: hthm where
  "IMP_ANTISYM_pth =
     the (do { let pq = mk_imp vp vq;
               let qp = mk_imp vq vp;
               a \<leftarrow> ASSUME (mk_conj pq qp);
               (pth1, pth2) \<leftarrow> CONJ_PAIR a;
               u2 \<leftarrow> UNDISCH pth2;
               u1 \<leftarrow> UNDISCH pth1;
               let pth3 = DEDUCT_ANTISYM_RULE u2 u1;
               aq \<leftarrow> ASSUME vq;
               pth4 \<leftarrow> DISCH_ALL aq;
               pth5 \<leftarrow> ASSUME (safe_mk_eq vp vq);
               t1 \<leftarrow> AP_TERM imp_c pth5;
               t2 \<leftarrow> AP_THM t1 vq;
               s \<leftarrow> SYM t2;
               x \<leftarrow> EQ_MP s pth4;
               iq \<leftarrow> mk_comb imp_c vq;
               u1' \<leftarrow> AP_TERM iq pth5;
               s' \<leftarrow> SYM u1';
               y \<leftarrow> EQ_MP s' pth4;
               pth6 \<leftarrow> CONJ x y;
               Some (DEDUCT_ANTISYM_RULE pth6 pth3) })"

definition IMP_ANTISYM_RULE :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "IMP_ANTISYM_RULE th1 th2 =
     do { (p1, q1) \<leftarrow> dest_imp (concl th1);
          i \<leftarrow> INST [(p1, vp), (q1, vq)] IMP_ANTISYM_pth;
          c \<leftarrow> CONJ th1 th2;
          EQ_MP i c }"

definition ADD_ASSUM :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "ADD_ASSUM tm th = do { d \<leftarrow> DISCH tm th; a \<leftarrow> ASSUME tm; MP d a }"

definition EQ_IMP_pth1 :: hthm where
  "EQ_IMP_pth1 =
     the (do { let peq = safe_mk_eq vp vq;
               a \<leftarrow> ASSUME peq; b \<leftarrow> ASSUME vp; m \<leftarrow> EQ_MP a b;
               d1 \<leftarrow> DISCH vp m; DISCH peq d1 })"

definition EQ_IMP_pth2 :: hthm where
  "EQ_IMP_pth2 =
     the (do { let peq = safe_mk_eq vp vq;
               a \<leftarrow> ASSUME peq; s \<leftarrow> SYM a; b \<leftarrow> ASSUME vq; m \<leftarrow> EQ_MP s b;
               d1 \<leftarrow> DISCH vq m; DISCH peq d1 })"

definition EQ_IMP_RULE :: "hthm \<Rightarrow> (hthm \<times> hthm) option" where
  "EQ_IMP_RULE th =
     do { (l, r) \<leftarrow> dest_iff (concl th);
          i1 \<leftarrow> INST [(l, vp), (r, vq)] EQ_IMP_pth1;
          i2 \<leftarrow> INST [(l, vp), (r, vq)] EQ_IMP_pth2;
          a \<leftarrow> MP i1 th;
          b \<leftarrow> MP i2 th;
          Some (a, b) }"

definition IMP_TRANS :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "IMP_TRANS th1 th2 =
     do { (x, y) \<leftarrow> dest_imp (concl th1);
          (y', z) \<leftarrow> dest_imp (concl th2);
          (if y \<noteq> y' then None
           else do { a \<leftarrow> ASSUME (mk_imp vp vq);
                     b \<leftarrow> ASSUME (mk_imp vq vr);
                     c \<leftarrow> ASSUME vp;
                     m1 \<leftarrow> MP a c;
                     m2 \<leftarrow> MP b m1;
                     d1 \<leftarrow> DISCH vp m2;
                     d2 \<leftarrow> DISCH (mk_imp vq vr) d1;
                     pth \<leftarrow> DISCH (mk_imp vp vq) d2;
                     i \<leftarrow> INST [(x, vp), (y, vq), (z, vr)] pth;
                     m \<leftarrow> MP i th1;
                     MP m th2 }) }"

subsection \<open>Rules for ALL\<close>

definition SPEC_pth :: hthm where
  "SPEC_pth =
     the (do { a \<leftarrow> AP_THM FORALL_DEF vPA;
               ass \<leftarrow> ASSUME (Comb (forall_c aty) vPA);
               th1 \<leftarrow> EQ_MP a ass;
               th1b \<leftarrow> CONV_RULE BETA_CONV th1;
               th2 \<leftarrow> AP_THM th1b vx;
               th3 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) th2;
               e \<leftarrow> EQT_ELIM th3;
               DISCH_ALL e })"

definition SPEC :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SPEC tm th =
     do { abs' \<leftarrow> rand (concl th);
          bv \<leftarrow> bndvar abs';
          (_, ty) \<leftarrow> dest_var bv;
          i \<leftarrow> PINST [(ty, aty)] [(abs', vPA), (tm, vx)] SPEC_pth;
          m \<leftarrow> MP i th;
          CONV_RULE BETA_CONV m }"

definition SPECL :: "hterm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SPECL tms th = foldl (\<lambda>acc t. do { a \<leftarrow> acc; SPEC t a }) (Some th) tms"

definition SPEC_VAR :: "hthm \<Rightarrow> (hterm \<times> hthm) option" where
  "SPEC_VAR th =
     do { bv0 \<leftarrow> Option.bind (rand (concl th)) bndvar;
          let bv = variant (thm_frees th) bv0;
          t \<leftarrow> SPEC bv th;
          Some (bv, t) }"

primrec SPEC_ALL_n :: "nat \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SPEC_ALL_n 0 th = Some th"
| "SPEC_ALL_n (Suc n) th =
     (if is_forall (concl th) then do { (_, th') \<leftarrow> SPEC_VAR th; SPEC_ALL_n n th' } else Some th)"

definition SPEC_ALL :: "hthm \<Rightarrow> hthm option" where
  "SPEC_ALL th = SPEC_ALL_n (tm_size (concl th)) th"

definition ISPEC :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "ISPEC t th =
     do { (x, _) \<leftarrow> dest_forall (concl th);
          (_, xty) \<leftarrow> dest_var x;
          tyins \<leftarrow> type_match xty (type_of t) [];
          th' \<leftarrow> INST_TYPE tyins th;
          SPEC t th' }"

definition GEN_pth :: hthm where
  "GEN_pth = the (do { a \<leftarrow> AP_THM FORALL_DEF vPA; b \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a; SYM b })"

definition GEN :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "GEN x th =
     do { (_, ty) \<leftarrow> dest_var x;
          qth \<leftarrow> INST_TYPE [(ty, aty)] GEN_pth;
          ptm \<leftarrow> Option.bind (rand (concl qth)) rand;
          e \<leftarrow> EQT_INTRO th;
          th' \<leftarrow> ABS x e;
          phi \<leftarrow> lhand (concl th');
          rth \<leftarrow> INST [(phi, ptm)] qth;
          EQ_MP rth th' }"

definition GENL :: "hterm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "GENL vs th = foldr (\<lambda>v acc. do { t \<leftarrow> acc; GEN v t }) vs (Some th)"

definition GEN_ALL :: "hthm \<Rightarrow> hthm option" where
  "GEN_ALL th = GENL (lsubtract (frees (concl th)) (freesl (hyp th))) th"

subsection \<open>Rules for EX\<close>

definition EXISTS_pth :: hthm where
  "EXISTS_pth =
     the (do { a \<leftarrow> AP_THM EXISTS_DEF vPA;
               th1 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a;
               let allh = mk_forall vx (mk_imp (Comb vPA vx) vQb);
               a2 \<leftarrow> ASSUME allh;
               th2 \<leftarrow> SPEC vx a2;
               ap \<leftarrow> ASSUME (Comb vPA vx);
               m \<leftarrow> MP th2 ap;
               th3 \<leftarrow> DISCH allh m;
               g \<leftarrow> GEN vQb th3;
               s \<leftarrow> SYM th1;
               EQ_MP s g })"

definition EXISTS :: "hterm \<times> hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "EXISTS p th =
     do { let etm = fst p; let stm = snd p;
          (_, abs') \<leftarrow> dest_comb etm;
          ab \<leftarrow> mk_comb abs' stm;
          bth \<leftarrow> BETA_CONV ab;
          cth \<leftarrow> PINST [(type_of stm, aty)] [(abs', vPA), (stm, vx)] EXISTS_pth;
          sb \<leftarrow> SYM bth;
          e \<leftarrow> EQ_MP sb th;
          PROVE_HYP e cth }"

definition SIMPLE_EXISTS :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SIMPLE_EXISTS v th = EXISTS (mk_exists v (concl th), v) th"

definition CHOOSE_pth :: hthm where
  "CHOOSE_pth =
     the (do { a \<leftarrow> AP_THM EXISTS_DEF vPA;
               th1 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a;
               (e1, _) \<leftarrow> EQ_IMP_RULE th1;
               u \<leftarrow> UNDISCH e1;
               th2 \<leftarrow> SPEC vQb u;
               ud \<leftarrow> UNDISCH th2;
               dd \<leftarrow> DISCH (Comb (exists_c aty) vPA) ud;
               DISCH_ALL dd })"

definition CHOOSE :: "hterm \<times> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CHOOSE p th2 =
     do { let v = fst p; let th1 = snd p;
          abs' \<leftarrow> rand (concl th1);
          (bv, bod) \<leftarrow> dest_abs abs';
          cmb \<leftarrow> mk_comb abs' v;
          let pat = vsubst [(v, bv)] bod;
          ac \<leftarrow> ASSUME cmb;
          th3 \<leftarrow> CONV_RULE BETA_CONV ac;
          d1 \<leftarrow> DISCH pat th2;
          m \<leftarrow> MP d1 th3;
          d2 \<leftarrow> DISCH cmb m;
          th4 \<leftarrow> GEN v d2;
          (_, vty) \<leftarrow> dest_var v;
          th5 \<leftarrow> PINST [(vty, aty)] [(abs', vPA), (concl th2, vQb)] CHOOSE_pth;
          m1 \<leftarrow> MP th5 th4;
          MP m1 th1 }"

definition SIMPLE_CHOOSE :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SIMPLE_CHOOSE v th =
     (case hyp th of
        h # _ \<Rightarrow> do { a \<leftarrow> ASSUME (mk_exists v h); CHOOSE (v, a) th }
      | [] \<Rightarrow> None)"

subsection \<open>Rules for OR\<close>

definition or_unfold :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "or_unfold p q =
     do { a1 \<leftarrow> AP_THM OR_DEF p;
          th1 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a1;
          a2 \<leftarrow> AP_THM th1 q;
          CONV_RULE (RAND_CONV BETA_CONV) a2 }"

definition DISJ_pth :: "bool \<Rightarrow> hthm" where
  "DISJ_pth left =
     the (do { th2 \<leftarrow> or_unfold vPb vQb;
               a \<leftarrow> ASSUME (mk_imp (if left then vPb else vQb) vt);
               b \<leftarrow> ASSUME (if left then vPb else vQb);
               th3 \<leftarrow> MP a b;
               d1 \<leftarrow> DISCH (mk_imp vQb vt) th3;
               d2 \<leftarrow> DISCH (mk_imp vPb vt) d1;
               th4 \<leftarrow> GEN vt d2;
               s \<leftarrow> SYM th2;
               EQ_MP s th4 })"

definition DISJ1 :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "DISJ1 th tm =
     do { i \<leftarrow> INST [(concl th, vPb), (tm, vQb)] (DISJ_pth True);
          EQ_MP (DEDUCT_ANTISYM_RULE th i) th }"

definition DISJ2 :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISJ2 tm th =
     do { i \<leftarrow> INST [(tm, vPb), (concl th, vQb)] (DISJ_pth False);
          EQ_MP (DEDUCT_ANTISYM_RULE th i) th }"

definition DISJ_CASES_pth :: hthm where
  "DISJ_CASES_pth =
     the (do { th2 \<leftarrow> or_unfold vPb vQb;
               a \<leftarrow> ASSUME (mk_disj vPb vQb);
               e \<leftarrow> EQ_MP th2 a;
               th3 \<leftarrow> SPEC vRb e;
               u1 \<leftarrow> UNDISCH th3;
               UNDISCH u1 })"

definition DISJ_CASES :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISJ_CASES th0 th1 th2 =
     (let c1 = concl th1; c2 = concl th2 in
      if \<not> aconv c1 c2 then None
      else
        do { (l, r) \<leftarrow> dest_disj (concl th0);
             th \<leftarrow> INST [(l, vPb), (r, vQb), (c1, vRb)] DISJ_CASES_pth;
             let e = DEDUCT_ANTISYM_RULE th0 th;
             e1 \<leftarrow> EQ_MP e th0;
             d1 \<leftarrow> DISCH l th1;
             p1 \<leftarrow> PROVE_HYP d1 e1;
             d2 \<leftarrow> DISCH r th2;
             PROVE_HYP d2 p1 })"

definition SIMPLE_DISJ_CASES :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SIMPLE_DISJ_CASES th1 th2 =
     (case (hyp th1, hyp th2) of
        (a # _, b # _) \<Rightarrow> do { x \<leftarrow> ASSUME (mk_disj a b); DISJ_CASES x th1 th2 }
      | _ \<Rightarrow> None)"

subsection \<open>Rules for negation and falsity\<close>

definition NOT_ELIM_pth :: hthm where
  "NOT_ELIM_pth = the (do { a \<leftarrow> AP_THM NOT_DEF vPb; CONV_RULE (RAND_CONV BETA_CONV) a })"

definition NOT_ELIM :: "hthm \<Rightarrow> hthm option" where
  "NOT_ELIM th =
     do { p \<leftarrow> rand (concl th); i \<leftarrow> INST [(p, vPb)] NOT_ELIM_pth; EQ_MP i th }"

definition NOT_INTRO_pth :: hthm where
  "NOT_INTRO_pth = the (do { a \<leftarrow> AP_THM NOT_DEF vPb; b \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a; SYM b })"

definition NOT_INTRO :: "hthm \<Rightarrow> hthm option" where
  "NOT_INTRO th =
     do { p \<leftarrow> Option.bind (rator (concl th)) rand; i \<leftarrow> INST [(p, vPb)] NOT_INTRO_pth; EQ_MP i th }"

definition EQF_INTRO_pth :: hthm where
  "EQF_INTRO_pth =
     the (do { a \<leftarrow> ASSUME (mk_neg vPb);
               th1 \<leftarrow> NOT_ELIM a;
               aF \<leftarrow> ASSUME F_tm;
               e \<leftarrow> EQ_MP F_DEF aF;
               s \<leftarrow> SPEC vPb e;
               th2 \<leftarrow> DISCH F_tm s;
               ia \<leftarrow> IMP_ANTISYM_RULE th1 th2;
               DISCH_ALL ia })"

definition EQF_INTRO :: "hthm \<Rightarrow> hthm option" where
  "EQF_INTRO th =
     do { p \<leftarrow> rand (concl th); i \<leftarrow> INST [(p, vPb)] EQF_INTRO_pth; MP i th }"

definition EQF_ELIM_pth :: hthm where
  "EQF_ELIM_pth =
     the (do { a \<leftarrow> ASSUME (safe_mk_eq vPb F_tm);
               b \<leftarrow> ASSUME vPb;
               th1 \<leftarrow> EQ_MP a b;
               e \<leftarrow> EQ_MP F_DEF th1;
               s \<leftarrow> SPEC F_tm e;
               th2 \<leftarrow> DISCH vPb s;
               n \<leftarrow> NOT_INTRO th2;
               DISCH_ALL n })"

definition EQF_ELIM :: "hthm \<Rightarrow> hthm option" where
  "EQF_ELIM th =
     do { p \<leftarrow> Option.bind (rator (concl th)) rand; i \<leftarrow> INST [(p, vPb)] EQF_ELIM_pth; MP i th }"

definition CONTR_pth :: hthm where
  "CONTR_pth = the (do { aF \<leftarrow> ASSUME F_tm; e \<leftarrow> EQ_MP F_DEF aF; SPEC vPb e })"

definition CONTR :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONTR tm th =
     (if concl th \<noteq> F_tm then None
      else do { i \<leftarrow> INST [(tm, vPb)] CONTR_pth; EQ_MP (DEDUCT_ANTISYM_RULE th i) th })"

subsection \<open>Unique existence\<close>

definition EXISTENCE :: "hthm \<Rightarrow> hthm option" where
  "EXISTENCE th =
     do { a1 \<leftarrow> AP_THM EXISTS_UNIQUE_DEF vPA;
          th1 \<leftarrow> CONV_RULE (RAND_CONV BETA_CONV) a1;
          (e1, _) \<leftarrow> EQ_IMP_RULE th1;
          th2 \<leftarrow> UNDISCH e1;
          c1 \<leftarrow> CONJUNCT1 th2;
          pth \<leftarrow> DISCH_ALL c1;
          abs' \<leftarrow> rand (concl th);
          bv \<leftarrow> bndvar abs';
          (_, ty) \<leftarrow> dest_var bv;
          i \<leftarrow> PINST [(ty, aty)] [(abs', vPA)] pth;
          MP i th }"

subsection \<open>Excluded middle and case analysis from the axiom\<close>

definition EXCLUDED_MIDDLE :: hthm where
  "EXCLUDED_MIDDLE =
     the (do { bc \<leftarrow> SPEC vt BOOL_CASES_AX;
               let eT = safe_mk_eq vt T_tm;
               let eF = safe_mk_eq vt F_tm;
               aT \<leftarrow> ASSUME eT;
               pT \<leftarrow> EQT_ELIM aT;
               c1 \<leftarrow> DISJ1 pT (mk_neg vt);
               aF \<leftarrow> ASSUME eF;
               ap \<leftarrow> ASSUME vt;
               fF \<leftarrow> EQ_MP aF ap;
               dd \<leftarrow> DISCH vt fF;
               np \<leftarrow> NOT_INTRO dd;
               c2 \<leftarrow> DISJ2 vt np;
               dc \<leftarrow> DISJ_CASES bc c1 c2;
               GEN vt dc })"

definition CCONTR :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CCONTR p th =
     do { em \<leftarrow> SPEC p EXCLUDED_MIDDLE;
          ap \<leftarrow> ASSUME p;
          c \<leftarrow> CONTR p th;
          DISJ_CASES em ap c }"


section \<open>Instantiation and higher-order matching (drule.ml)\<close>

type_synonym instn =
  "(nat \<times> hterm) list \<times> (hterm \<times> hterm) list \<times> (hol_type \<times> hol_type) list"

primrec BETAS_CONV :: "nat \<Rightarrow> conv" where
  "BETAS_CONV 0 tm = None"
| "BETAS_CONV (Suc n) tm =
     (if n = 0 then TRY_CONV BETA_CONV tm
      else THENC (RATOR_CONV (BETAS_CONV n)) (TRY_CONV BETA_CONV) tm)"

text \<open>@{text HO_BETAS}: after a higher-order instantiation, beta-reduce the instantiated
  pattern applications.  Recursion is on the pattern.\<close>

fun ho_betas :: "(nat \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "ho_betas bcs (Var _ _) tm = None"
| "ho_betas bcs (Const _ _) tm = None"
| "ho_betas bcs (Abs pv pb) tm =
     (case tm of
        Abs bv bod \<Rightarrow> (case ho_betas bcs pb bod of Some th \<Rightarrow> ABS bv th | None \<Rightarrow> None)
      | _ \<Rightarrow> None)"
| "ho_betas bcs (Comb lpat rpat) tm =
     (let (hop, args) = strip_comb (Comb lpat rpat);
          direct = (case rev_assoc hop bcs of
                      Some n \<Rightarrow> if length args = n then BETAS_CONV n tm else None
                    | None \<Rightarrow> None)
      in case direct of
           Some th \<Rightarrow> Some th
         | None \<Rightarrow>
             (case tm of
                Comb ltm rtm \<Rightarrow>
                  (case ho_betas bcs lpat ltm of
                     Some lth \<Rightarrow>
                       (case ho_betas bcs rpat rtm of
                          Some rth \<Rightarrow> (case MK_COMB lth rth of Some r \<Rightarrow> Some r | None \<Rightarrow> AP_THM lth rtm)
                        | None \<Rightarrow> AP_THM lth rtm)
                   | None \<Rightarrow>
                       (case ho_betas bcs rpat rtm of
                          Some rth \<Rightarrow> AP_TERM ltm rth
                        | None \<Rightarrow> None))
              | _ \<Rightarrow> None))"

definition INSTANTIATE :: "instn \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "INSTANTIATE i th =
     (case i of (bcs, tmin, tyin) \<Rightarrow>
        do { ith \<leftarrow> (if tyin = [] then Some th else INST_TYPE tyin th);
             (if tmin = [] then Some ith
              else
                do { tth \<leftarrow> INST tmin ith;
                     (if hyp tth = hyp th
                      then (if bcs = [] then Some tth
                            else (case ho_betas bcs (concl ith) (concl tth) of
                                    Some eth \<Rightarrow> (case EQ_MP eth tth of Some r \<Rightarrow> Some r | None \<Rightarrow> Some tth)
                                  | None \<Rightarrow> Some tth))
                      else None) }) })"

subsection \<open>Higher-order matching of terms\<close>

definition safe_inserta :: "hterm \<times> hterm \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> (hterm \<times> hterm) list option" where
  "safe_inserta n l =
     (case rev_assoc (snd n) l of
        Some z \<Rightarrow> if aconv (fst n) z then Some l else None
      | None \<Rightarrow> Some (n # l))"

definition safe_insert :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list option" where
  "safe_insert n l =
     (case rev_assoc (snd n) l of
        Some z \<Rightarrow> if fst n = z then Some l else None
      | None \<Rightarrow> Some (n # l))"

definition mk_dummy :: "hol_type \<Rightarrow> hterm" where "mk_dummy ty = Var ''_'' ty"

definition head_of :: "hterm \<Rightarrow> hterm" where "head_of t = fst (strip_comb t)"

type_synonym homs = "((hterm \<times> hterm) list \<times> hterm \<times> hterm) list"

fun term_pmatch ::
  "hterm list \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> (hterm \<times> hterm) list \<times> homs \<Rightarrow>
   ((hterm \<times> hterm) list \<times> homs) option" where
  "term_pmatch lconsts env (Var n ty) ctm (insts, homs) =
     (let vtm = Var n ty in
      case rev_assoc vtm env of
        Some ctm' \<Rightarrow> if ctm' = ctm then Some (insts, homs) else None
      | None \<Rightarrow>
          (if vtm \<in> set lconsts then (if ctm = vtm then Some (insts, homs) else None)
           else (case safe_inserta (ctm, vtm) insts of Some i \<Rightarrow> Some (i, homs) | None \<Rightarrow> None)))"
| "term_pmatch lconsts env (Const vn vty) ctm (insts, homs) =
     (case ctm of
        Const cn cty \<Rightarrow>
          (if vn = cn
           then (if vty = cty then Some (insts, homs)
                 else (case safe_insert (mk_dummy cty, mk_dummy vty) insts of
                         Some i \<Rightarrow> Some (i, homs) | None \<Rightarrow> None))
           else None)
      | _ \<Rightarrow> None)"
| "term_pmatch lconsts env (Abs vv vbod) ctm (insts, homs) =
     (case ctm of
        Abs cv cbod \<Rightarrow>
          (case (vv, cv) of
             (Var _ vty, Var _ cty) \<Rightarrow>
               (case safe_insert (mk_dummy cty, mk_dummy vty) insts of
                  Some i \<Rightarrow> term_pmatch lconsts ((cv, vv) # env) vbod cbod (i, homs)
                | None \<Rightarrow> None)
           | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"
| "term_pmatch lconsts env (Comb lv rv) ctm (insts, homs) =
     (let vtm = Comb lv rv; vhop = head_of vtm in
      if is_var vhop \<and> vhop \<notin> set lconsts \<and> rev_assoc vhop env = None
      then
        (let vty = type_of vtm; cty = type_of ctm in
         case (if vty = cty then Some insts else safe_insert (mk_dummy cty, mk_dummy vty) insts) of
           Some insts' \<Rightarrow> Some (insts', (env, ctm, vtm) # homs)
         | None \<Rightarrow> None)
      else
        (case ctm of
           Comb lc rc \<Rightarrow>
             (case term_pmatch lconsts env lv lc (insts, homs) of
                Some sofar' \<Rightarrow> term_pmatch lconsts env rv rc sofar'
              | None \<Rightarrow> None)
         | _ \<Rightarrow> None))"

definition get_type_insts :: "(hterm \<times> hterm) list \<Rightarrow> (hol_type \<times> hol_type) list option" where
  "get_type_insts insts =
     foldr (\<lambda>p acc.
              do { a \<leftarrow> acc;
                   (_, xty) \<leftarrow> dest_var (snd p);
                   type_match xty (type_of (fst p)) a })
           insts (Some [])"

definition separate_insts ::
  "(hterm \<times> hterm) list \<Rightarrow> instn option" where
  "separate_insts insts =
     (let realinsts = filter (\<lambda>p. is_var (snd p)) insts;
          patterns = filter (\<lambda>p. \<not> is_var (snd p)) insts;
          betacounts =
            foldr (\<lambda>p sof.
                     (let (hop, args) = strip_comb (snd p) in
                      case rev_assoc hop sof of
                        Some n \<Rightarrow> if n = length args then sof else sof
                      | None \<Rightarrow> (length args, hop) # sof))
                  patterns []
      in do { tyins \<leftarrow> get_type_insts realinsts;
              let tm_pairs = List.map_filter
                    (\<lambda>p. (case snd p of
                            Var xn xty \<Rightarrow>
                              (let x' = Var xn (type_subst tyins xty) in
                               if fst p = x' then None else Some (fst p, x'))
                          | _ \<Rightarrow> None)) realinsts;
              Some (betacounts, tm_pairs, tyins) })"

text \<open>One step of @{text term_homatch} (the part inside OCaml's @{text try}).\<close>

definition homatch_step ::
  "hterm list \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow>
   (hterm \<times> hterm) list \<Rightarrow> (hterm \<times> hterm) list option" where
  "homatch_step lconsts tyins env ctm vtm insts =
     (let (vhop, vargs) = strip_comb vtm;
          afvs = freesl vargs
      in do { tmins \<leftarrow> those (map (\<lambda>a.
                          (case (case rev_assoc a env of
                                   Some v \<Rightarrow> Some v
                                 | None \<Rightarrow> (case rev_assoc a insts of
                                             Some v \<Rightarrow> Some v
                                           | None \<Rightarrow> if a \<in> set lconsts then Some a else None)) of
                             Some v \<Rightarrow> map_option (\<lambda>ia. (v, ia)) (inst tyins a)
                           | None \<Rightarrow> None)) afvs);
              pats0 \<leftarrow> those (map (inst tyins) vargs);
              pats \<leftarrow> those (map (\<lambda>p. vsubst_checked tmins p) pats0);
              vhop' \<leftarrow> inst tyins vhop;
              let (chop, cargs) = strip_comb ctm;
              (if cargs = pats
               then (if chop = vhop then Some insts else safe_inserta (chop, vhop) insts)
               else
                 do { let ginsts = snd (foldl (\<lambda>(av, acc) p.
                                          (let g = (if is_var p then p else genvar (av @ [ctm]) (type_of p))
                                           in (av @ [g], acc @ [(g, p)]))) ([], []) pats);
                      ctm' \<leftarrow> subst ginsts ctm;
                      let gvs = map fst ginsts;
                      abstm \<leftarrow> list_mk_abs gvs ctm';
                      vinsts \<leftarrow> safe_inserta (abstm, vhop) insts;
                      app \<leftarrow> list_mk_comb vhop' gvs;
                      Some ((ctm', app) # vinsts) }) })"

partial_function (option) term_homatch ::
  "hterm list \<Rightarrow> (hol_type \<times> hol_type) list \<Rightarrow> (hterm \<times> hterm) list \<times> homs \<Rightarrow>
   (hterm \<times> hterm) list option option" where
  "term_homatch lconsts tyins ih =
     (case ih of
        (insts, homs) \<Rightarrow>
          (case homs of
             [] \<Rightarrow> Some (Some insts)
           | (env, ctm, vtm) # rest \<Rightarrow>
               (if is_var vtm then
                  (if ctm = vtm then term_homatch lconsts tyins (insts, rest)
                   else
                     (case (case dest_var vtm of
                              Some (_, vty) \<Rightarrow> safe_insert (type_of ctm, vty) tyins
                            | None \<Rightarrow> None) of
                        Some newtyins \<Rightarrow> term_homatch lconsts newtyins ((ctm, vtm) # insts, rest)
                      | None \<Rightarrow> Some None))
                else
                  do { r \<leftarrow> (case homatch_step lconsts tyins env ctm vtm insts of
                              Some ni \<Rightarrow> term_homatch lconsts tyins (ni, rest)
                            | None \<Rightarrow> Some None);
                       (case r of
                          Some x \<Rightarrow> Some (Some x)
                        | None \<Rightarrow>
                            (case (ctm, vtm) of
                               (Comb lc rc, Comb lv rv) \<Rightarrow>
                                 (case term_pmatch lconsts env rv rc (insts, (env, lc, lv) # rest) of
                                    Some pih \<Rightarrow>
                                      (case get_type_insts (fst pih) of
                                         Some tyins' \<Rightarrow> term_homatch lconsts tyins' pih
                                       | None \<Rightarrow> Some None)
                                  | None \<Rightarrow> Some None)
                             | _ \<Rightarrow> Some None)) })))"

declare term_homatch.simps [code]

definition term_match :: "hterm list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> instn option" where
  "term_match lconsts vtm ctm =
     do { pih \<leftarrow> term_pmatch lconsts [] vtm ctm ([], []);
          tyins \<leftarrow> get_type_insts (fst pih);
          r \<leftarrow> term_homatch lconsts tyins pih;
          (case r of None \<Rightarrow> None | Some insts \<Rightarrow> separate_insts insts) }"

subsection \<open>PART_MATCH\<close>

text \<open>Bound-variable renaming at depth.\<close>

definition tryalpha :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "tryalpha v tm =
     (case alpha v tm of
        Some t \<Rightarrow> t
      | None \<Rightarrow> (case alpha (variant (frees tm) v) tm of Some t \<Rightarrow> t | None \<Rightarrow> tm))"

definition remove_first_by :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option" where
  "remove_first_by p l =
     (case find p l of
        None \<Rightarrow> None
      | Some x \<Rightarrow> (let i = length (takeWhile (\<lambda>y. \<not> p y) l) in Some (x, take i l @ drop (Suc i) l)))"

text \<open>@{text deep_alpha} recurses on the body of the renamed abstraction, which is not
  structurally smaller; it is a partial function (@{text None} is non-termination).\<close>

partial_function (option) deep_alpha_p :: "(string \<times> string) list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "deep_alpha_p env tm =
     (if env = [] then Some tm
      else
        (case tm of
           Abs v bod \<Rightarrow>
             (case v of
                Var vn vty \<Rightarrow>
                  (case remove_first_by (\<lambda>p. snd p = vn) env of
                     Some ((vn', _), newenv) \<Rightarrow>
                       (case tryalpha (Var vn' vty) tm of
                          Abs iv ib \<Rightarrow> do { r \<leftarrow> deep_alpha_p newenv ib; Some (Abs iv r) }
                        | _ \<Rightarrow> do { r \<leftarrow> deep_alpha_p env bod; Some (Abs v r) })
                   | None \<Rightarrow> do { r \<leftarrow> deep_alpha_p env bod; Some (Abs v r) })
              | _ \<Rightarrow> Some tm)
         | Comb l r \<Rightarrow>
             do { a \<leftarrow> deep_alpha_p env l; b \<leftarrow> deep_alpha_p env r; Some (Comb a b) }
         | _ \<Rightarrow> Some tm))"

declare deep_alpha_p.simps [code]

definition deep_alpha :: "(string \<times> string) list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "deep_alpha env tm = (case deep_alpha_p env tm of Some t \<Rightarrow> t | None \<Rightarrow> tm)"

fun match_bvs :: "hterm \<Rightarrow> hterm \<Rightarrow> (string \<times> string) list \<Rightarrow> (string \<times> string) list" where
  "match_bvs (Abs v1 b1) (Abs v2 b2) acc =
     (let n1 = var_name v1; n2 = var_name v2;
          newacc = (if n1 = n2 then acc else List.insert (n1, n2) acc)
      in match_bvs b1 b2 newacc)"
| "match_bvs (Comb l1 r1) (Comb l2 r2) acc = match_bvs l1 l2 (match_bvs r1 r2 acc)"
| "match_bvs _ _ acc = acc"

definition PART_MATCH :: "(hterm \<Rightarrow> hterm option) \<Rightarrow> hthm \<Rightarrow> conv" where
  "PART_MATCH partfn th tm =
     do { sth \<leftarrow> SPEC_ALL th;
          let bod = concl sth;
          pbod \<leftarrow> partfn bod;
          let lconsts = List.filter (\<lambda>x. x \<in> set (freesl (hyp th))) (frees (concl th));
          let bvms = match_bvs tm pbod [];
          let abod = deep_alpha bvms bod;
          al \<leftarrow> ALPHA bod abod;
          ath \<leftarrow> EQ_MP al sth;
          pa \<leftarrow> partfn abod;
          insts \<leftarrow> term_match lconsts pa tm;
          fth \<leftarrow> INSTANTIATE insts ath;
          (if hyp fth \<noteq> hyp ath then None
           else
             do { tm' \<leftarrow> partfn (concl fth);
                  (if tm' = tm then Some fth
                   else do { a2 \<leftarrow> ALPHA tm' tm; SUBS [a2] fth }) }) }"


section \<open>Rewriting conversions (simp.ml)\<close>

definition REWR_CONV :: "hthm \<Rightarrow> conv" where
  "REWR_CONV = PART_MATCH (\<lambda>tm. map_option fst (dest_eq tm))"

definition IMP_REWR_CONV :: "hthm \<Rightarrow> conv" where
  "IMP_REWR_CONV =
     PART_MATCH (\<lambda>tm. Option.bind (dest_imp tm) (\<lambda>p. map_option fst (dest_eq (snd p))))"

definition ORDERED_REWR_CONV :: "(hterm \<Rightarrow> hterm \<Rightarrow> bool) \<Rightarrow> hthm \<Rightarrow> conv" where
  "ORDERED_REWR_CONV ord th tm =
     do { thm \<leftarrow> REWR_CONV th tm;
          (l, r) \<leftarrow> dest_eq (concl thm);
          (if ord l r then Some thm else None) }"

definition ORDERED_IMP_REWR_CONV :: "(hterm \<Rightarrow> hterm \<Rightarrow> bool) \<Rightarrow> hthm \<Rightarrow> conv" where
  "ORDERED_IMP_REWR_CONV ord th tm =
     do { thm \<leftarrow> IMP_REWR_CONV th tm;
          r \<leftarrow> rand (concl thm);
          (l, r') \<leftarrow> dest_eq r;
          (if ord l r' then Some thm else None) }"

text \<open>The standard "dynamic" lexicographic term ordering: with identical head operator the
  operator is stuck at the front of an otherwise arbitrary ordering on subterms.\<close>

fun lexify :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "lexify ord [] l2 = False"
| "lexify ord (h1 # t1) [] = True"
| "lexify ord (h1 # t1) (h2 # t2) = (ord h1 h2 \<or> (h1 = h2 \<and> lexify ord t1 t2))"

primrec dyn_order_n :: "nat \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "dyn_order_n 0 tp tm1 tm2 = False"
| "dyn_order_n (Suc k) tp tm1 tm2 =
     (let (f1, args1) = strip_comb tm1; (f2, args2) = strip_comb tm2 in
      if f1 = f2 then lexify (dyn_order_n k f1) args1 args2
      else if f2 = tp then False
      else if f1 = tp then True
      else cmp_tm f1 f2 = CGt)"

definition term_order :: "hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "term_order tm1 tm2 = dyn_order_n (tm_size tm1 + tm_size tm2 + 1) T_tm tm1 tm2"

text \<open>Rewrite nets.  HOL Light indexes rewrites in a discrimination net; here a net is the
  list of its entries and @{text lookup} selects those whose pattern is net-compatible
  with the term (constants must agree in name and arity, variables are wildcards), ordered
  as the net traversal would return them.\<close>

record rwentry =
  re_lconsts :: "hterm list"
  re_pat :: hterm
  re_prio :: nat
  re_conv :: conv

primrec net_label_match :: "nat \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> bool" where
  "net_label_match 0 lconsts pat tm = True"
| "net_label_match (Suc k) lconsts pat tm =
     (let (pop, pargs) = strip_comb pat; (tp, targs) = strip_comb tm in
      case pop of
        Const pn _ \<Rightarrow>
          (case tp of
             Const tn _ \<Rightarrow> pn = tn \<and> length pargs = length targs
                          \<and> list_all (\<lambda>p. net_label_match k lconsts (fst p) (snd p)) (zip pargs targs)
           | _ \<Rightarrow> False)
      | Abs _ pb \<Rightarrow>
          (case tp of
             Abs _ tb \<Rightarrow> length pargs = length targs
                        \<and> net_label_match k lconsts pb tb
                        \<and> list_all (\<lambda>p. net_label_match k lconsts (fst p) (snd p)) (zip pargs targs)
           | _ \<Rightarrow> False)
      | Var pn _ \<Rightarrow>
          (if pop \<in> set lconsts
           then (case tp of
                   Var tn _ \<Rightarrow> pn = tn \<and> length pargs = length targs
                              \<and> list_all (\<lambda>p. net_label_match k lconsts (fst p) (snd p)) (zip pargs targs)
                 | _ \<Rightarrow> False)
           else True)
      | Comb _ _ \<Rightarrow> True)"

text \<open>Specificity key of a pattern along the traversal: constant branches come before the
  variable branch.\<close>

primrec net_key :: "nat \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> nat list" where
  "net_key 0 lconsts pat = []"
| "net_key (Suc k) lconsts pat =
     (let (pop, pargs) = strip_comb pat in
      case pop of
        Var _ _ \<Rightarrow> if pop \<in> set lconsts then 0 # concat (map (net_key k lconsts) pargs) else [1]
      | _ \<Rightarrow> 0 # concat (map (net_key k lconsts) pargs))"

fun insert_key :: "'a \<times> nat list \<Rightarrow> ('a \<times> nat list) list \<Rightarrow> ('a \<times> nat list) list" where
  "insert_key x [] = [x]"
| "insert_key x (y # ys) = (if cmp_list (snd x) (snd y) = CLt then x # y # ys else y # insert_key x ys)"

fun sort_by_key :: "('a \<times> nat list) list \<Rightarrow> ('a \<times> nat list) list" where
  "sort_by_key [] = []"
| "sort_by_key (x # xs) = insert_key x (sort_by_key xs)"

definition lookup :: "hterm \<Rightarrow> rwentry list \<Rightarrow> rwentry list" where
  "lookup tm net =
     (let cands = filter (\<lambda>e. net_label_match (tm_size tm + tm_size (re_pat e) + 1) (re_lconsts e) (re_pat e) tm) net in
      map fst (sort_by_key (rev (map (\<lambda>e. (e, net_key (tm_size (re_pat e) + 1) (re_lconsts e) (re_pat e))) cands))))"

definition enter :: "hterm list \<Rightarrow> hterm \<times> nat \<times> conv \<Rightarrow> rwentry list \<Rightarrow> rwentry list" where
  "enter lconsts p net =
     net @ [\<lparr> re_lconsts = lconsts, re_pat = fst p, re_prio = fst (snd p), re_conv = snd (snd p) \<rparr>]"

definition net_of_thm :: "bool \<Rightarrow> hthm \<Rightarrow> rwentry list \<Rightarrow> rwentry list" where
  "net_of_thm rep th net =
     (let tm = concl th; lconsts = freesl (hyp th);
          matchable = (\<lambda>a b. term_match lconsts a b \<noteq> None)
      in case tm of
           Comb (Comb (Const eqn _) l) r \<Rightarrow>
             (if eqn \<noteq> ''='' then net
              else
                (case (l, r) of
                   (Abs x (Comb (Var s ty) x'), v') \<Rightarrow>
                     (if x' = x \<and> v' = Var s ty \<and> x \<noteq> Var s ty
                      then enter lconsts (l, 1, (\<lambda>tm.
                             (case tm of
                                Abs y (Comb t y') \<Rightarrow>
                                  (if y = y' \<and> \<not> free_in y t
                                   then (do { i \<leftarrow> term_match [] (Var s ty) t; INSTANTIATE i th })
                                   else None)
                              | _ \<Rightarrow> None))) net
                      else
                        (if rep \<and> free_in l r then
                           (case EQT_INTRO th of Some th' \<Rightarrow> enter lconsts (l, 1, REWR_CONV th') net | None \<Rightarrow> net)
                         else if rep \<and> matchable l r \<and> matchable r l
                         then enter lconsts (l, 1, ORDERED_REWR_CONV term_order th) net
                         else enter lconsts (l, 1, REWR_CONV th) net))
                 | _ \<Rightarrow>
                     (if rep \<and> free_in l r then
                        (case EQT_INTRO th of Some th' \<Rightarrow> enter lconsts (l, 1, REWR_CONV th') net | None \<Rightarrow> net)
                      else if rep \<and> matchable l r \<and> matchable r l
                      then enter lconsts (l, 1, ORDERED_REWR_CONV term_order th) net
                      else enter lconsts (l, 1, REWR_CONV th) net)))
         | Comb (Comb _ t) (Comb (Comb (Const eqn _) l) r) \<Rightarrow>
             (if eqn \<noteq> ''='' then net
              else
                (if rep \<and> free_in l r then
                   (case do { u \<leftarrow> UNDISCH th; e \<leftarrow> EQT_INTRO u; DISCH t e } of
                      Some th' \<Rightarrow> enter lconsts (l, 3, IMP_REWR_CONV th') net | None \<Rightarrow> net)
                 else if rep \<and> matchable l r \<and> matchable r l
                 then enter lconsts (l, 3, ORDERED_IMP_REWR_CONV term_order th) net
                 else enter lconsts (l, 3, IMP_REWR_CONV th) net))
         | _ \<Rightarrow> net)"

text \<open>Rewrite maker for ordinary rewrites (the @{text cf} = false case of
  @{text mk_rewrites}): strip quantifiers, split conjunctions, turn @{text "~ p"} into
  @{text "p = F"} (and @{text "(t = s) = F"} for negated equations), other propositions
  into @{text "p = T"}.  The conditional case (@{text cf} = true, used by the full
  simplifier only) is not needed by the rewriter and not ported.\<close>

primrec split_rewrites_n :: "nat \<Rightarrow> hthm \<Rightarrow> hthm list \<Rightarrow> hthm list" where
  "split_rewrites_n 0 th sofar = sofar"
| "split_rewrites_n (Suc n) th sofar =
     (let tm = concl th in
      if is_forall tm then
        (case SPEC_ALL th of Some th' \<Rightarrow> split_rewrites_n n th' sofar | None \<Rightarrow> sofar)
      else if is_conj tm then
        (case (CONJUNCT1 th, CONJUNCT2 th) of
           (Some a, Some b) \<Rightarrow> split_rewrites_n n a (split_rewrites_n n b sofar)
         | _ \<Rightarrow> sofar)
      else if dest_eq tm \<noteq> None then th # sofar
      else if is_neg tm then
        (case EQF_INTRO th of
           Some e \<Rightarrow>
             (let ths = split_rewrites_n n e sofar in
              case Option.bind (rand tm) dest_eq of
                Some _ \<Rightarrow> (case do { g \<leftarrow> GSYM th; EQF_INTRO g } of
                            Some e2 \<Rightarrow> split_rewrites_n n e2 ths
                          | None \<Rightarrow> ths)
              | None \<Rightarrow> ths)
         | None \<Rightarrow> sofar)
      else (case EQT_INTRO th of Some e \<Rightarrow> split_rewrites_n n e sofar | None \<Rightarrow> sofar))"

definition mk_rewrites :: "hthm \<Rightarrow> hthm list \<Rightarrow> hthm list" where
  "mk_rewrites th sofar = split_rewrites_n (tm_size (concl th) + 3) th sofar"

definition REWRITES_CONV :: "rwentry list \<Rightarrow> conv" where
  "REWRITES_CONV net tm =
     foldl (\<lambda>acc e. case acc of Some th \<Rightarrow> Some th | None \<Rightarrow> re_conv e tm) None (lookup tm net)"

definition GENERAL_REWRITE_CONV :: "bool \<Rightarrow> (conv \<Rightarrow> conv) \<Rightarrow> rwentry list \<Rightarrow> hthm list \<Rightarrow> conv" where
  "GENERAL_REWRITE_CONV rep cnvl builtin_net thl =
     (let thl_canon = foldr mk_rewrites thl [];
          final_net = foldr (net_of_thm rep) thl_canon builtin_net
      in cnvl (REWRITES_CONV final_net))"

definition GEN_REWRITE_CONV :: "(conv \<Rightarrow> conv) \<Rightarrow> hthm list \<Rightarrow> conv" where
  "GEN_REWRITE_CONV cnvl thl = GENERAL_REWRITE_CONV False cnvl [] thl"

definition PURE_REWRITE_CONV :: "hthm list \<Rightarrow> conv" where
  "PURE_REWRITE_CONV thl = GENERAL_REWRITE_CONV True TOP_DEPTH_CONV [] thl"

definition PURE_ONCE_REWRITE_CONV :: "hthm list \<Rightarrow> conv" where
  "PURE_ONCE_REWRITE_CONV thl = GENERAL_REWRITE_CONV False ONCE_DEPTH_CONV [] thl"


section \<open>Bootstrap propositional prover\<close>

text \<open>HOL Light proves its first propositional clause theorems with the intuitionistic
  tableau prover @{text ITAUT} (@{text itab.ml}).  Here a small prover by ground evaluation and
  case splitting on atoms plays that role; it is used only to prove the clause theorems that
  seed the basic rewrites and the proforma equations of the CNF conversion.\<close>

fun gval :: "hterm \<Rightarrow> bool option" where
  "gval (Const n ty) = (if n = ''T'' then Some True else if n = ''F'' then Some False else None)"
| "gval (Comb (Const n _) a) = (if n = ''NOT'' then map_option Not (gval a) else None)"
| "gval (Comb (Comb (Const n _) a) b) =
     (case (gval a, gval b) of
        (Some x, Some y) \<Rightarrow>
          (if n = ''AND'' then Some (x \<and> y)
           else if n = ''OR'' then Some (x \<or> y)
           else if n = ''IMP'' then Some (x \<longrightarrow> y)
           else if n = ''='' \<and> type_of a = bool_ty then Some (x = y)
           else None)
      | _ \<Rightarrow> None)"
| "gval _ = None"

text \<open>@{text pt}: a proof of a ground formula that evaluates to true; @{text ph}: a proof
  of @{text F} from a ground formula that evaluates to false; @{text eqv}: the equation
  @{text "tm = T"} or @{text "tm = F"}.\<close>

fun pt :: "hterm \<Rightarrow> hthm option"
and ph :: "hterm \<Rightarrow> hthm option"
and eqv :: "hterm \<Rightarrow> hthm option" where
  "pt tm =
     (if tm = T_tm then Some TRUTH
      else case tm of
        Comb (Const n _) a \<Rightarrow>
          (if n = ''NOT'' then do { d \<leftarrow> ph a; dd \<leftarrow> DISCH a d; NOT_INTRO dd } else None)
      | Comb (Comb (Const n _) a) b \<Rightarrow>
          (if n = ''AND'' then do { x \<leftarrow> pt a; y \<leftarrow> pt b; CONJ x y }
           else if n = ''OR'' then
             (if gval a = Some True then do { x \<leftarrow> pt a; DISJ1 x b }
              else do { y \<leftarrow> pt b; DISJ2 a y })
           else if n = ''IMP'' then
             (if gval a = Some False then do { d \<leftarrow> ph a; c \<leftarrow> CONTR b d; DISCH a c }
              else do { y \<leftarrow> pt b; DISCH a y })
           else if n = ''='' then
             do { ea \<leftarrow> eqv a; eb \<leftarrow> eqv b; seb \<leftarrow> SYM eb; TRANS ea seb }
           else None)
      | _ \<Rightarrow> None)"
| "ph tm =
     (if tm = F_tm then ASSUME F_tm
      else case tm of
        Comb (Const n _) a \<Rightarrow>
          (if n = ''NOT'' then
             do { at \<leftarrow> ASSUME tm; ne \<leftarrow> NOT_ELIM at; x \<leftarrow> pt a; MP ne x }
           else None)
      | Comb (Comb (Const n _) a) b \<Rightarrow>
          (if n = ''AND'' then
             (if gval a = Some False
              then do { at \<leftarrow> ASSUME tm; c1 \<leftarrow> CONJUNCT1 at; d \<leftarrow> ph a; PROVE_HYP c1 d }
              else do { at \<leftarrow> ASSUME tm; c2 \<leftarrow> CONJUNCT2 at; d \<leftarrow> ph b; PROVE_HYP c2 d })
           else if n = ''OR'' then
             do { at \<leftarrow> ASSUME tm; da \<leftarrow> ph a; db \<leftarrow> ph b; DISJ_CASES at da db }
           else if n = ''IMP'' then
             do { at \<leftarrow> ASSUME tm; x \<leftarrow> pt a; m \<leftarrow> MP at x; d \<leftarrow> ph b; PROVE_HYP m d }
           else if n = ''='' then
             do { at \<leftarrow> ASSUME tm;
                  (if gval a = Some True
                   then do { pa \<leftarrow> pt a; m \<leftarrow> EQ_MP at pa; d \<leftarrow> ph b; PROVE_HYP m d }
                   else do { sa \<leftarrow> SYM at; pb \<leftarrow> pt b; m \<leftarrow> EQ_MP sa pb; d \<leftarrow> ph a; PROVE_HYP m d }) }
           else None)
      | _ \<Rightarrow> None)"
| "eqv tm =
     (case gval tm of
        Some True \<Rightarrow> do { x \<leftarrow> pt tm; EQT_INTRO x }
      | Some False \<Rightarrow>
          do { d \<leftarrow> ph tm;
               aF \<leftarrow> ASSUME F_tm;
               c \<leftarrow> CONTR tm aF;
               Some (DEDUCT_ANTISYM_RULE c d) }
      | None \<Rightarrow> None)"


text \<open>Replacement of all occurrences of the left-hand side of an equation by its right-hand
  side, with proof: @{text "\<turnstile> tm = tm[b/a]"}.\<close>

primrec replace_conv :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "replace_conv th (Var n ty) =
     (case lhs th of Some a \<Rightarrow> if aconv a (Var n ty) then Some th else Some (REFL (Var n ty)) | None \<Rightarrow> None)"
| "replace_conv th (Const n ty) =
     (case lhs th of Some a \<Rightarrow> if aconv a (Const n ty) then Some th else Some (REFL (Const n ty)) | None \<Rightarrow> None)"
| "replace_conv th (Comb s t) =
     (case lhs th of
        Some a \<Rightarrow>
          if aconv a (Comb s t) then Some th
          else do { th1 \<leftarrow> replace_conv th s; th2 \<leftarrow> replace_conv th t; MK_COMB th1 th2 }
      | None \<Rightarrow> None)"
| "replace_conv th (Abs v b) =
     (case lhs th of
        Some a \<Rightarrow>
          if aconv a (Abs v b) then Some th
          else do { th1 \<leftarrow> replace_conv th b; ABS v th1 }
      | None \<Rightarrow> None)"

fun bool_atoms :: "hterm \<Rightarrow> hterm list" where
  "bool_atoms tm =
     (if tm = T_tm \<or> tm = F_tm then []
      else case tm of
        Comb (Const n _) a \<Rightarrow> (if n = ''NOT'' then bool_atoms a else [tm])
      | Comb (Comb (Const n _) a) b \<Rightarrow>
          (if n = ''AND'' \<or> n = ''OR'' \<or> n = ''IMP'' \<or> (n = ''='' \<and> type_of a = bool_ty)
           then List.union (bool_atoms a) (bool_atoms b)
           else [tm])
      | _ \<Rightarrow> [tm])"

primrec taut_n :: "nat \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "taut_n 0 t = None"
| "taut_n (Suc n) t =
     (case bool_atoms t of
        [] \<Rightarrow> (if gval t = Some True then pt t else None)
      | a # _ \<Rightarrow>
          do { bc \<leftarrow> SPEC a BOOL_CASES_AX;
               let eT = safe_mk_eq a T_tm;
               let eF = safe_mk_eq a F_tm;
               aT \<leftarrow> ASSUME eT;
               aF \<leftarrow> ASSUME eF;
               rT \<leftarrow> replace_conv aT t;
               rF \<leftarrow> replace_conv aF t;
               tT \<leftarrow> rhs rT;
               tF \<leftarrow> rhs rF;
               pT \<leftarrow> taut_n n tT;
               pF \<leftarrow> taut_n n tF;
               srT \<leftarrow> SYM rT;
               srF \<leftarrow> SYM rF;
               c1 \<leftarrow> EQ_MP srT pT;
               c2 \<leftarrow> EQ_MP srF pF;
               DISJ_CASES bc c1 c2 })"

definition BS_TAUT :: "hterm \<Rightarrow> hthm option" where
  "BS_TAUT t = taut_n (Suc (length (bool_atoms t))) t"


section \<open>Basic rewrites (theorems.ml, class.ml)\<close>

text \<open>The clause theorems that HOL Light installs as basic rewrites.\<close>

definition bty :: hol_type where "bty = Tyvar ''B''"

definition clause_thm :: "hterm \<Rightarrow> hthm" where
  "clause_thm tm = the (do { th \<leftarrow> BS_TAUT tm; GEN vt th })"

definition REFL_CLAUSE :: hthm where
  "REFL_CLAUSE = the (do { e \<leftarrow> EQT_INTRO (REFL vx); GEN vx e })"

definition EQ_CLAUSES :: hthm where
  "EQ_CLAUSES =
     clause_thm
       (mk_conj (mk_iff (mk_iff T_tm vt) vt)
          (mk_conj (mk_iff (mk_iff vt T_tm) vt)
             (mk_conj (mk_iff (mk_iff F_tm vt) (mk_neg vt))
                      (mk_iff (mk_iff vt F_tm) (mk_neg vt)))))"

definition NOT_CLAUSES_WEAK :: hthm where
  "NOT_CLAUSES_WEAK =
     the (BS_TAUT (mk_conj (mk_iff (mk_neg T_tm) F_tm) (mk_iff (mk_neg F_tm) T_tm)))"

definition AND_CLAUSES :: hthm where
  "AND_CLAUSES =
     clause_thm
       (mk_conj (mk_iff (mk_conj T_tm vt) vt)
          (mk_conj (mk_iff (mk_conj vt T_tm) vt)
             (mk_conj (mk_iff (mk_conj F_tm vt) F_tm)
                (mk_conj (mk_iff (mk_conj vt F_tm) F_tm) (mk_iff (mk_conj vt vt) vt)))))"

definition OR_CLAUSES :: hthm where
  "OR_CLAUSES =
     clause_thm
       (mk_conj (mk_iff (mk_disj T_tm vt) T_tm)
          (mk_conj (mk_iff (mk_disj vt T_tm) T_tm)
             (mk_conj (mk_iff (mk_disj F_tm vt) vt)
                (mk_conj (mk_iff (mk_disj vt F_tm) vt) (mk_iff (mk_disj vt vt) vt)))))"

definition IMP_CLAUSES :: hthm where
  "IMP_CLAUSES =
     clause_thm
       (mk_conj (mk_iff (mk_imp T_tm vt) vt)
          (mk_conj (mk_iff (mk_imp vt T_tm) T_tm)
             (mk_conj (mk_iff (mk_imp F_tm vt) T_tm)
                (mk_conj (mk_iff (mk_imp vt vt) T_tm) (mk_iff (mk_imp vt F_tm) (mk_neg vt))))))"

definition NOT_CLAUSES :: hthm where
  "NOT_CLAUSES =
     the (do { a \<leftarrow> BS_TAUT (mk_iff (mk_neg (mk_neg vt)) vt);
               g \<leftarrow> GEN vt a;
               b \<leftarrow> BS_TAUT (mk_conj (mk_iff (mk_neg T_tm) F_tm) (mk_iff (mk_neg F_tm) T_tm));
               CONJ g b })"

definition FORALL_SIMP :: hthm where
  "FORALL_SIMP =
     the (do { a \<leftarrow> ASSUME (mk_forall vx vt);
               th1 \<leftarrow> SPEC vx a;
               b \<leftarrow> ASSUME vt;
               th2 \<leftarrow> GEN vx b;
               let e = DEDUCT_ANTISYM_RULE th2 th1;
               GEN vt e })"

definition EXISTS_SIMP :: hthm where
  "EXISTS_SIMP =
     the (do { a \<leftarrow> ASSUME (mk_exists vx vt);
               b \<leftarrow> ASSUME vt;
               th1 \<leftarrow> CHOOSE (vx, a) b;
               th2 \<leftarrow> EXISTS (mk_exists vx vt, vx) b;
               let e = DEDUCT_ANTISYM_RULE th2 th1;
               GEN vt e })"

definition BETA_THM :: hthm where
  "BETA_THM =
     (let f = Var ''f'' (fun_ty aty bty); y = Var ''y'' aty in
      the (do { b \<leftarrow> BETA_CONV (Comb (Abs vx (Comb f vx)) y); GENL [f, y] b }))"

definition IMP_EQ_CLAUSE :: hthm where
  "IMP_EQ_CLAUSE =
     the (do { r \<leftarrow> EQT_INTRO (REFL vx);
               c \<leftarrow> SPEC vp IMP_CLAUSES;
               c1 \<leftarrow> CONJUNCT1 c;
               a \<leftarrow> AP_TERM imp_c r;
               b \<leftarrow> MK_COMB a (REFL vp);
               TRANS b c1 })"

text \<open>HOL Light's @{text basic_rewrites} at the time @{text TAUT} is defined: the clause
  theorems above together with @{text "~ ~ t = t"}.\<close>

definition basic_rewrites :: "hthm list" where
  "basic_rewrites =
     foldr mk_rewrites [the (CONJUNCT1 NOT_CLAUSES)] []
     @ foldr mk_rewrites
         [REFL_CLAUSE, EQ_CLAUSES, NOT_CLAUSES_WEAK, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES,
          FORALL_SIMP, EXISTS_SIMP, BETA_THM, IMP_EQ_CLAUSE] []"

definition basic_net :: "rwentry list" where
  "basic_net = foldr (net_of_thm True) basic_rewrites []"

definition REWRITE_CONV :: "hthm list \<Rightarrow> conv" where
  "REWRITE_CONV thl = GENERAL_REWRITE_CONV True TOP_DEPTH_CONV basic_net thl"

definition ONCE_REWRITE_CONV :: "hthm list \<Rightarrow> conv" where
  "ONCE_REWRITE_CONV thl = GENERAL_REWRITE_CONV False ONCE_DEPTH_CONV basic_net thl"


section \<open>Tactics (tactics.ml; the metavariable-free subset)\<close>

text \<open>A goal has labelled assumptions; a tactic maps a goal to subgoals together with a
  justification.  HOL Light's tactics additionally thread metavariables and an instantiation
  (used by @{text ITAUT} and @{text MESON}); none of the tactics ported here introduces a
  metavariable, so that component is omitted.\<close>

type_synonym goal = "(string \<times> hthm) list \<times> hterm"
type_synonym justification = "hthm list \<Rightarrow> hthm option"
type_synonym goalstate = "goal list \<times> justification"
type_synonym tactic = "goal \<Rightarrow> goalstate option"
type_synonym thm_tactic = "hthm \<Rightarrow> tactic"

definition ALL_TAC_state :: "goal \<Rightarrow> goalstate" where
  "ALL_TAC_state g = ([g], (\<lambda>ths. case ths of [th] \<Rightarrow> Some th | _ \<Rightarrow> None))"

definition ALL_TAC :: tactic where "ALL_TAC g = Some (ALL_TAC_state g)"

definition FAIL_TAC :: "string \<Rightarrow> tactic" where "FAIL_TAC tok g = None"
definition NO_TAC :: tactic where "NO_TAC = FAIL_TAC ''NO_TAC''"

fun chop_apply :: "(nat \<times> justification) list \<Rightarrow> hthm list \<Rightarrow> hthm list option" where
  "chop_apply [] ths = (if ths = [] then Some [] else None)"
| "chop_apply ((n, j) # r) ths =
     (if n \<le> length ths
      then do { a \<leftarrow> j (take n ths); b \<leftarrow> chop_apply r (drop n ths); Some (a # b) }
      else None)"

definition compose_states :: "goal list \<times> justification \<Rightarrow> goalstate list \<Rightarrow> goalstate" where
  "compose_states st sts =
     (concat (map fst sts),
      (\<lambda>ths. do { rs \<leftarrow> chop_apply (map (\<lambda>s. (length (fst s), snd s)) sts) ths; snd st rs }))"

definition THEN :: "tactic \<Rightarrow> tactic \<Rightarrow> tactic" where
  "THEN tac1 tac2 g =
     do { st \<leftarrow> tac1 g; sts \<leftarrow> those (map tac2 (fst st)); Some (compose_states st sts) }"

definition THENL :: "tactic \<Rightarrow> tactic list \<Rightarrow> tactic" where
  "THENL tac1 tacs g =
     do { st \<leftarrow> tac1 g;
          (if fst st = [] then Some (compose_states st [])
           else if length tacs \<noteq> length (fst st) then None
           else do { sts \<leftarrow> those (map (\<lambda>p. fst p (snd p)) (zip tacs (fst st)));
                     Some (compose_states st sts) }) }"

definition ORELSE :: "tactic \<Rightarrow> tactic \<Rightarrow> tactic" where
  "ORELSE tac1 tac2 g = (case tac1 g of Some r \<Rightarrow> Some r | None \<Rightarrow> tac2 g)"

definition TRY :: "tactic \<Rightarrow> tactic" where "TRY tac = ORELSE tac ALL_TAC"

definition EVERY :: "tactic list \<Rightarrow> tactic" where "EVERY tacl = foldr THEN tacl ALL_TAC"

fun FIRST :: "tactic list \<Rightarrow> tactic" where
  "FIRST [] = NO_TAC"
| "FIRST [t] = t"
| "FIRST (t # ts) = ORELSE t (FIRST ts)"

text \<open>@{text REPEAT}: @{text "REPEAT tac g = ((tac THEN REPEAT tac) ORELSE ALL_TAC) g"} loops
  until the tactic fails, so it is a partial function (outer @{const None} = nontermination).
  It is written over lists of goals so that its recursion goes through itself only.  The result
  is the list of goalstates, one per goal.\<close>

partial_function (option) repeat_tac :: "tactic \<Rightarrow> goal list \<Rightarrow> goalstate list option option" where
  "repeat_tac tac goals =
     (case goals of
        [] \<Rightarrow> Some (Some [])
      | g # gs \<Rightarrow>
          do { st \<leftarrow> (case tac g of
                       None \<Rightarrow> Some (Some (ALL_TAC_state g))
                     | Some stg \<Rightarrow>
                         do { sub \<leftarrow> repeat_tac tac (fst stg);
                              (case sub of
                                 None \<Rightarrow> Some (Some (ALL_TAC_state g))
                               | Some sts \<Rightarrow> Some (Some (compose_states stg sts))) });
               rest \<leftarrow> repeat_tac tac gs;
               Some (case rest of
                       None \<Rightarrow> None
                     | Some r \<Rightarrow> (case st of Some s \<Rightarrow> Some (s # r) | None \<Rightarrow> None)) })"

declare repeat_tac.simps [code]

definition REPEAT :: "tactic \<Rightarrow> tactic" where
  "REPEAT tac g = (case repeat_tac tac [g] of Some (Some [st]) \<Rightarrow> Some st | _ \<Rightarrow> None)"

definition ASSUME_TAC :: thm_tactic where
  "ASSUME_TAC thm g =
     (case g of (asl, w) \<Rightarrow>
        Some ([(('''', thm) # asl, w)], (\<lambda>ths. case ths of [th] \<Rightarrow> PROVE_HYP thm th | _ \<Rightarrow> None)))"

definition POP_ASSUM :: "thm_tactic \<Rightarrow> tactic" where
  "POP_ASSUM ttac g =
     (case g of ((_, th) # asl, w) \<Rightarrow> ttac th (asl, w) | _ \<Rightarrow> None)"

definition ACCEPT_TAC :: thm_tactic where
  "ACCEPT_TAC th g =
     (case g of (asl, w) \<Rightarrow>
        if aconv (concl th) w then Some ([], (\<lambda>ths. if ths = [] then Some th else None)) else None)"

definition CONV_TAC :: "conv \<Rightarrow> tactic" where
  "CONV_TAC conv g =
     (case g of (asl, w) \<Rightarrow>
        do { th \<leftarrow> conv w;
             let tm = concl th;
             (if aconv tm w then ACCEPT_TAC th g
              else
                do { (l, r) \<leftarrow> dest_eq tm;
                     (if \<not> aconv l w then None
                      else if r = T_tm then do { e \<leftarrow> EQT_ELIM th; ACCEPT_TAC e g }
                      else do { th' \<leftarrow> SYM th;
                                Some ([(asl, r)], (\<lambda>ths. case ths of [t] \<Rightarrow> EQ_MP th' t | _ \<Rightarrow> None)) }) }) })"

definition SUBST1_TAC :: thm_tactic where
  "SUBST1_TAC th = CONV_TAC (SUBS_CONV [th])"

definition REWRITE_TAC :: "hthm list \<Rightarrow> tactic" where
  "REWRITE_TAC thl = CONV_TAC (REWRITE_CONV thl)"

text \<open>Variable names for @{text GEN_TAC}: like HOL Light's @{text mk_primed_var} this avoids
  the given variables and the names of constants (here those of the logical theory).\<close>

definition reserved_names :: "string list" where
  "reserved_names = [''='', ''T'', ''F'', ''NOT'', ''AND'', ''OR'', ''IMP'', ''ALL'', ''EX'', ''EXU'']"

primrec svariant :: "nat \<Rightarrow> string list \<Rightarrow> string \<Rightarrow> string" where
  "svariant 0 avoid s = s"
| "svariant (Suc n) avoid s =
     (if s \<in> set avoid \<or> s \<in> set reserved_names then svariant n avoid (s @ [CHR 0x27]) else s)"

definition mk_primed_var :: "hterm list \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_primed_var avoid v =
     (case v of
        Var s ty \<Rightarrow>
          (let names = List.map_filter (\<lambda>a. case a of Var n _ \<Rightarrow> Some n | _ \<Rightarrow> None) avoid in
           Some (Var (svariant (length names + length reserved_names + 1) names s) ty))
      | _ \<Rightarrow> None)"

definition goal_avoids :: "goal \<Rightarrow> hterm list" where
  "goal_avoids g = foldr (\<lambda>p acc. List.union (thm_frees (snd p)) acc) (fst g) (frees (snd g))"

definition X_GEN_TAC :: "hterm \<Rightarrow> tactic" where
  "X_GEN_TAC x' g =
     (case g of (asl, w) \<Rightarrow>
        (if \<not> is_var x' then None
         else
           do { (x, bod) \<leftarrow> dest_forall w;
                (if type_of x \<noteq> type_of x' then None
                 else if x' \<in> set (goal_avoids g) then None
                 else
                   Some ([(asl, vsubst [(x', x)] bod)],
                         (\<lambda>ths. case ths of
                                  [th] \<Rightarrow> do { gth \<leftarrow> GEN x' th; CONV_RULE (GEN_ALPHA_CONV x) gth }
                                | _ \<Rightarrow> None))) }))"

definition GEN_TAC :: tactic where
  "GEN_TAC g =
     (case g of (asl, w) \<Rightarrow>
        do { (x, _) \<leftarrow> dest_forall w;
             x' \<leftarrow> mk_primed_var (goal_avoids g) x;
             X_GEN_TAC x' g })"

definition CONJ_TAC :: tactic where
  "CONJ_TAC g =
     (case g of (asl, w) \<Rightarrow>
        do { (l, r) \<leftarrow> dest_conj w;
             Some ([(asl, l), (asl, r)], (\<lambda>ths. case ths of [a, b] \<Rightarrow> CONJ a b | _ \<Rightarrow> None)) })"

definition DISJ_CASES_TAC :: thm_tactic where
  "DISJ_CASES_TAC dth g =
     (case g of (asl, w) \<Rightarrow>
        do { (l, r) \<leftarrow> dest_disj (concl dth);
             thl \<leftarrow> ASSUME l;
             thr \<leftarrow> ASSUME r;
             Some ([(('''', thl) # asl, w), (('''', thr) # asl, w)],
                   (\<lambda>ths. case ths of [th1, th2] \<Rightarrow> DISJ_CASES dth th1 th2 | _ \<Rightarrow> None)) })"

definition X_CHOOSE_TAC :: "hterm \<Rightarrow> thm_tactic" where
  "X_CHOOSE_TAC x' xth g =
     (case g of (asl, w) \<Rightarrow>
        do { (x, bod) \<leftarrow> dest_exists (concl xth);
             (if \<not> is_var x' \<or> type_of x \<noteq> type_of x' then None
              else
                (let pat = vsubst [(x', x)] bod;
                     avoids = foldr (\<lambda>p acc. List.union (thm_frees (snd p)) acc) asl
                                    (List.union (frees w) (thm_frees xth))
                 in if x' \<in> set avoids then None
                    else do { xth' \<leftarrow> ASSUME pat;
                              Some ([(('''', xth') # asl, w)],
                                    (\<lambda>ths. case ths of [th] \<Rightarrow> CHOOSE (x', xth) th | _ \<Rightarrow> None)) })) })"

definition CHOOSE_TAC :: thm_tactic where
  "CHOOSE_TAC xth g =
     (case g of (asl, w) \<Rightarrow>
        do { (x, _) \<leftarrow> dest_exists (concl xth);
             let avoids = foldr (\<lambda>p acc. List.union (thm_frees (snd p)) acc) asl
                                (List.union (frees w) (thm_frees xth));
             x' \<leftarrow> mk_primed_var avoids x;
             X_CHOOSE_TAC x' xth g })"

subsection \<open>Theorem continuations and @{text STRUCT_CASES_TAC}\<close>

definition CONJUNCTS_THEN2 :: "thm_tactic \<Rightarrow> thm_tactic \<Rightarrow> thm_tactic" where
  "CONJUNCTS_THEN2 ttac1 ttac2 cth gl =
     do { (c1, c2) \<leftarrow> dest_conj (concl cth);
          a1 \<leftarrow> ASSUME c1;
          a2 \<leftarrow> ASSUME c2;
          (gls, jfn) \<leftarrow> THEN (ttac1 a1) (ttac2 a2) gl;
          Some (gls, (\<lambda>ths. do { (th1, th2) \<leftarrow> CONJ_PAIR cth;
                                 r \<leftarrow> jfn ths;
                                 x \<leftarrow> PROVE_HYP th2 r;
                                 PROVE_HYP th1 x })) }"

definition DISJ_CASES_THEN2 :: "thm_tactic \<Rightarrow> thm_tactic \<Rightarrow> thm_tactic" where
  "DISJ_CASES_THEN2 ttac1 ttac2 cth =
     THENL (DISJ_CASES_TAC cth) [POP_ASSUM ttac1, POP_ASSUM ttac2]"

text \<open>@{text STRUCT_CASES_THEN} recurses on the shape of the theorem (conjunction, disjunction,
  existential); the recursion is bounded by the term size.\<close>

primrec struct_cases_n :: "nat \<Rightarrow> thm_tactic \<Rightarrow> thm_tactic" where
  "struct_cases_n 0 ttac th = ttac th"
| "struct_cases_n (Suc k) ttac th =
     (if is_conj (concl th) then CONJUNCTS_THEN2 (struct_cases_n k ttac) (struct_cases_n k ttac) th
      else if dest_disj (concl th) \<noteq> None then
        DISJ_CASES_THEN2 (struct_cases_n k ttac) (struct_cases_n k ttac) th
      else if dest_exists (concl th) \<noteq> None then
        THEN (CHOOSE_TAC th) (POP_ASSUM (struct_cases_n k ttac))
      else ttac th)"

definition STRUCT_CASES_THEN :: "thm_tactic \<Rightarrow> thm_tactic" where
  "STRUCT_CASES_THEN ttac th = struct_cases_n (tm_size (concl th) + 1) ttac th"

definition STRUCT_CASES_TAC :: thm_tactic where
  "STRUCT_CASES_TAC =
     STRUCT_CASES_THEN (\<lambda>th. ORELSE (SUBST1_TAC th) (ASSUME_TAC th))"

definition BOOL_CASES_TAC :: "hterm \<Rightarrow> tactic" where
  "BOOL_CASES_TAC p g = do { th \<leftarrow> SPEC p BOOL_CASES_AX; STRUCT_CASES_TAC th g }"

subsection \<open>Proving\<close>

definition TAC_PROOF :: "goal \<times> tactic \<Rightarrow> hthm option" where
  "TAC_PROOF p =
     (case p of (g, tac) \<Rightarrow>
        (if type_of (snd g) \<noteq> bool_ty then None
         else
           do { (sgs, just) \<leftarrow> tac g; (if sgs = [] then just [] else None) }))"

definition prove :: "hterm \<Rightarrow> tactic \<Rightarrow> hthm option" where
  "prove t tac =
     do { th \<leftarrow> TAC_PROOF (([], t), tac);
          (if hyp th \<noteq> [] then None
           else if concl th = t then Some th
           else do { al \<leftarrow> ALPHA (concl th) t; EQ_MP al th }) }"

section \<open>Tautology prover (class.ml)\<close>

primrec contains_var :: "hterm \<Rightarrow> bool" where
  "contains_var (Var _ _) = True"
| "contains_var (Const _ _) = False"
| "contains_var (Comb s t) = (contains_var s \<or> contains_var t)"
| "contains_var (Abs _ b) = contains_var b"

text \<open>HOL Light's @{text sort}: pivot partition; used to find a term free in the others.\<close>

primrec sort_n :: "nat \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sort_n 0 cmp l = l"
| "sort_n (Suc n) cmp l =
     (case l of
        [] \<Rightarrow> []
      | piv # rest \<Rightarrow>
          (let r = filter (cmp piv) rest; l' = filter (\<lambda>x. \<not> cmp piv x) rest
           in sort_n n cmp l' @ (piv # sort_n n cmp r)))"

definition sort_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sort_by cmp l = sort_n (length l + 1) cmp l"

definition RTAUT_TAC :: tactic where
  "RTAUT_TAC g =
     THEN (REWRITE_TAC [])
          (\<lambda>g'. (let w = snd g';
                     ok = (\<lambda>t. type_of t = bool_ty \<and> contains_var t \<and> free_in t w)
                 in case sort_by free_in (find_terms ok w) of
                      [] \<Rightarrow> None
                    | t # _ \<Rightarrow> BOOL_CASES_TAC t g'))
          g"

definition TAUT_TAC :: tactic where
  "TAUT_TAC = THEN (REPEAT (ORELSE GEN_TAC CONJ_TAC)) (REPEAT RTAUT_TAC)"

definition TAUT :: "hterm \<Rightarrow> hthm option" where
  "TAUT tm = prove tm TAUT_TAC"

end
