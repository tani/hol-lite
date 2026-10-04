theory HOL_Lite_Bool
  imports HOL_Lite_Kernel "HOL-Library.Monad_Syntax"
begin


text \<open>
  Derived inference rules in the style of HOL Light's @{text equal.ml} and @{text bool.ml}:
  the propositional connectives and the universal quantifier are introduced by the
  kernel's definitional principle, and the usual natural-deduction rules are derived from
  the ten primitive rules.  Names of the logical constants are plain ASCII
  (@{text T}, @{text AND}, @{text IMP}, @{text ALL}, @{text OR}, @{text F}, @{text NOT}).

  The single classical axiom is @{text BOOL_CASES_AX}; in HOL Light it is derived from
  the axiom of choice (class.ml).
\<close>

section \<open>Term and theorem helpers\<close>

definition rator :: "hterm \<Rightarrow> hterm option" where
  "rator tm = map_option fst (dest_comb tm)"

definition rand :: "hterm \<Rightarrow> hterm option" where
  "rand tm = map_option snd (dest_comb tm)"

definition lhs :: "hthm \<Rightarrow> hterm option" where
  "lhs th = map_option fst (dest_eq (concl th))"

definition rhs :: "hthm \<Rightarrow> hterm option" where
  "rhs th = map_option snd (dest_eq (concl th))"

definition bb_ty :: hol_type where "bb_ty = fun_ty bool_ty bool_ty"
definition bbb_ty :: hol_type where "bbb_ty = fun_ty bool_ty (fun_ty bool_ty bool_ty)"

definition mk_eq :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_eq l r = (if type_of l = type_of r then Some (safe_mk_eq l r) else None)"

definition T_tm :: hterm where "T_tm = Const ''T'' bool_ty"
definition F_tm :: hterm where "F_tm = Const ''F'' bool_ty"
definition mk_not :: "hterm \<Rightarrow> hterm" where "mk_not p = Comb (Const ''NOT'' bb_ty) p"
definition mk_conj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_conj p q = Comb (Comb (Const ''AND'' bbb_ty) p) q"
definition mk_disj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_disj p q = Comb (Comb (Const ''OR'' bbb_ty) p) q"
definition mk_imp :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_imp p q = Comb (Comb (Const ''IMP'' bbb_ty) p) q"
definition mk_forall :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_forall v body =
     (case v of Var _ ty \<Rightarrow> Comb (Const ''ALL'' (fun_ty (fun_ty ty bool_ty) bool_ty)) (Abs v body)
              | _ \<Rightarrow> body)"

fun dest_binop :: "string \<Rightarrow> hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_binop c (Comb (Comb (Const n _) l) r) = (if n = c then Some (l, r) else None)"
| "dest_binop _ _ = None"

definition dest_conj :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_conj = dest_binop ''AND''"
definition dest_disj :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_disj = dest_binop ''OR''"
definition dest_imp :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where "dest_imp = dest_binop ''IMP''"

fun dest_neg :: "hterm \<Rightarrow> hterm option" where
  "dest_neg (Comb (Const n _) p) = (if n = ''NOT'' then Some p else None)"
| "dest_neg _ = None"

fun dest_forall :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_forall (Comb (Const n _) (Abs v b)) = (if n = ''ALL'' then Some (v, b) else None)"
| "dest_forall _ = None"

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
      else ''('' @ c @ '' (fn '' @ pp_tm v @ ''. '' @ pp_tm b @ ''))'')"
| "pp_tm (Comb (Const c _) a) = (if c = ''NOT'' then ''~'' @ pp_tm a else ''('' @ c @ '' '' @ pp_tm a @ '')'')"
| "pp_tm (Comb s t) = ''('' @ pp_tm s @ '' '' @ pp_tm t @ '')''"
| "pp_tm (Abs v b) = ''(fn '' @ pp_tm v @ ''. '' @ pp_tm b @ '')''"

definition pp_thm :: "hthm \<Rightarrow> string" where
  "pp_thm th = sep_by '', '' (map pp_tm (hyp th)) @ '' |- '' @ pp_tm (concl th)"

section \<open>Equational rules (equal.ml)\<close>

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

definition TRANS' :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where "TRANS' = TRANS"

definition BETA_CONV :: "hterm \<Rightarrow> hthm option" where
  "BETA_CONV tm =
     (case BETA tm of
        Some th \<Rightarrow> Some th
      | None \<Rightarrow>
          do { (f, arg) \<leftarrow> dest_comb tm;
               (v, _) \<leftarrow> dest_abs f;
               fv \<leftarrow> mk_comb f v;
               th1 \<leftarrow> BETA fv;
               INST [(arg, v)] th1 })"

definition PROVE_HYP :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "PROVE_HYP ath bth =
     (if list_ex (aconv (concl ath)) (hyp bth)
      then EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
      else Some bth)"

text \<open>Head beta-normalisation: @{text "\<turnstile> tm = tm'"}.\<close>

primrec beta_head_n :: "nat \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "beta_head_n 0 tm = Some (REFL tm)"
| "beta_head_n (Suc n) tm =
     (case tm of
        Comb f x \<Rightarrow>
          do { thf \<leftarrow> beta_head_n n f;
               th1 \<leftarrow> AP_THM thf x;
               r \<leftarrow> rhs th1;
               (case r of
                  Comb (Abs _ _) _ \<Rightarrow>
                    do { th2 \<leftarrow> BETA_CONV r;
                         r2 \<leftarrow> rhs th2;
                         th3 \<leftarrow> beta_head_n n r2;
                         th4 \<leftarrow> TRANS th1 th2;
                         TRANS th4 th3 }
                | _ \<Rightarrow> Some th1) }
      | _ \<Rightarrow> Some (REFL tm))"

definition beta_head :: "hterm \<Rightarrow> hthm option" where "beta_head = beta_head_n 40"

section \<open>Definitions of the logical constants\<close>

definition mk_defn :: "string \<Rightarrow> hol_type \<Rightarrow> hterm \<Rightarrow> hterm" where
  "mk_defn name ty r = safe_mk_eq (Var name ty) r"

definition vp :: hterm where "vp = Var ''p'' bool_ty"
definition vq :: hterm where "vq = Var ''q'' bool_ty"
definition vr :: hterm where "vr = Var ''r'' bool_ty"
definition vf :: hterm where "vf = Var ''f'' bbb_ty"

definition and_c :: hterm where "and_c = Const ''AND'' bbb_ty"
definition imp_c :: hterm where "imp_c = Const ''IMP'' bbb_ty"
definition or_c :: hterm where "or_c = Const ''OR'' bbb_ty"
definition not_c :: hterm where "not_c = Const ''NOT'' bb_ty"

definition t_def_tm :: hterm where
  "t_def_tm = mk_defn ''T'' bool_ty (safe_mk_eq (Abs vp vp) (Abs vp vp))"

definition and_def_tm :: hterm where
  "and_def_tm = mk_defn ''AND'' bbb_ty
     (Abs vp (Abs vq (safe_mk_eq (Abs vf (Comb (Comb vf vp) vq)) (Abs vf (Comb (Comb vf T_tm) T_tm)))))"

definition imp_def_tm :: hterm where
  "imp_def_tm = mk_defn ''IMP'' bbb_ty (Abs vp (Abs vq (safe_mk_eq (mk_conj vp vq) vp)))"

definition vA :: hterm where "vA = Var ''P'' (fun_ty aty bool_ty)"
definition vx :: hterm where "vx = Var ''x'' aty"

definition all_ty :: hol_type where "all_ty = fun_ty (fun_ty aty bool_ty) bool_ty"

definition forall_def_tm :: hterm where
  "forall_def_tm = mk_defn ''ALL'' all_ty (Abs vA (safe_mk_eq vA (Abs vx T_tm)))"

definition or_def_tm :: hterm where
  "or_def_tm = mk_defn ''OR'' bbb_ty
     (Abs vp (Abs vq (mk_forall vr (mk_imp (mk_imp vp vr) (mk_imp (mk_imp vq vr) vr)))))"

definition f_def_tm :: hterm where
  "f_def_tm = mk_defn ''F'' bool_ty (mk_forall vp vp)"

definition not_def_tm :: hterm where
  "not_def_tm = mk_defn ''NOT'' bb_ty (Abs vp (mk_imp vp F_tm))"

definition bool_cases_tm :: hterm where
  "bool_cases_tm =
     (let t = Var ''t'' bool_ty in
      mk_forall t (mk_disj (safe_mk_eq t T_tm) (safe_mk_eq t F_tm)))"

text \<open>Run all definitions through the kernel, producing the kernel state of the logic
  together with the defining theorems.\<close>

definition bool_init :: "(kstate \<times> hthm list) option" where
  "bool_init =
     do { (k1, t1) \<leftarrow> new_basic_definition init_kstate t_def_tm;
          (k2, t2) \<leftarrow> new_basic_definition k1 and_def_tm;
          (k3, t3) \<leftarrow> new_basic_definition k2 imp_def_tm;
          (k4, t4) \<leftarrow> new_basic_definition k3 forall_def_tm;
          (k5, t5) \<leftarrow> new_basic_definition k4 or_def_tm;
          (k6, t6) \<leftarrow> new_basic_definition k5 f_def_tm;
          (k7, t7) \<leftarrow> new_basic_definition k6 not_def_tm;
          (k8, t8) \<leftarrow> new_axiom k7 bool_cases_tm;
          Some (k8, [t1, t2, t3, t4, t5, t6, t7, t8]) }"

definition bool_kstate :: kstate where "bool_kstate = fst (the bool_init)"

definition bthm :: "nat \<Rightarrow> hthm" where "bthm i = (snd (the bool_init)) ! i"

definition T_DEF :: hthm where "T_DEF = bthm 0"
definition AND_DEF :: hthm where "AND_DEF = bthm 1"
definition IMP_DEF :: hthm where "IMP_DEF = bthm 2"
definition FORALL_DEF :: hthm where "FORALL_DEF = bthm 3"
definition OR_DEF :: hthm where "OR_DEF = bthm 4"
definition F_DEF :: hthm where "F_DEF = bthm 5"
definition NOT_DEF :: hthm where "NOT_DEF = bthm 6"
definition BOOL_CASES_AX :: hthm where "BOOL_CASES_AX = bthm 7"

section \<open>Derived rules (bool.ml)\<close>

definition TRUTH :: hthm where
  "TRUTH = the (do { s \<leftarrow> SYM T_DEF; EQ_MP s (REFL (Abs vp vp)) })"

definition EQT_ELIM :: "hthm \<Rightarrow> hthm option" where
  "EQT_ELIM th = do { s \<leftarrow> SYM th; EQ_MP s TRUTH }"

definition EQT_INTRO :: "hthm \<Rightarrow> hthm" where
  "EQT_INTRO th = DEDUCT_ANTISYM_RULE th TRUTH"

text \<open>Chain of equations.\<close>

definition TRANS3 :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "TRANS3 a b c = do { ab \<leftarrow> TRANS a b; TRANS ab c }"

definition SYM_TRANS :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SYM_TRANS a b = do { sa \<leftarrow> SYM a; TRANS sa b }"

text \<open>Unfolding a definition applied to arguments, then beta-reducing the result.\<close>

definition unfold_app :: "hthm \<Rightarrow> hterm list \<Rightarrow> hthm option" where
  "unfold_app def args =
     do { th0 \<leftarrow> foldl (\<lambda>acc a. do { t \<leftarrow> acc; AP_THM t a }) (Some def) args;
          r \<leftarrow> rhs th0;
          nf \<leftarrow> beta_head r;
          TRANS th0 nf }"

definition inst_all :: "hthm \<Rightarrow> hol_type \<Rightarrow> hthm option" where
  "inst_all th ty = INST_TYPE [(ty, aty)] th"

definition FORALL_UNFOLD :: "hterm \<Rightarrow> hol_type \<Rightarrow> hthm option" where
  "FORALL_UNFOLD P ty = do { d \<leftarrow> inst_all FORALL_DEF ty; unfold_app d [P] }"

definition AND_UNFOLD :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "AND_UNFOLD p q = unfold_app AND_DEF [p, q]"

definition IMP_UNFOLD :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "IMP_UNFOLD p q = unfold_app IMP_DEF [p, q]"

definition OR_UNFOLD :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "OR_UNFOLD p q = unfold_app OR_DEF [p, q]"

definition NOT_UNFOLD :: "hterm \<Rightarrow> hthm option" where
  "NOT_UNFOLD p = unfold_app NOT_DEF [p]"

definition GEN :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "GEN x th =
     (case x of
        Var _ ty \<Rightarrow>
          do { let e = EQT_INTRO th;
               ab \<leftarrow> ABS x e;
               l \<leftarrow> lhs ab;
               unf \<leftarrow> FORALL_UNFOLD l ty;
               su \<leftarrow> SYM unf;
               EQ_MP su ab }
      | _ \<Rightarrow> None)"

definition GENL :: "hterm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "GENL vs th = foldr (\<lambda>v acc. do { t \<leftarrow> acc; GEN v t }) vs (Some th)"

definition SPEC :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SPEC tm th =
     (case dest_forall (concl th) of
        None \<Rightarrow> None
      | Some (x, _) \<Rightarrow>
          (case x of
             Var _ ty \<Rightarrow>
               do { P \<leftarrow> rand (concl th);
                    unf \<leftarrow> FORALL_UNFOLD P ty;
                    eq \<leftarrow> EQ_MP unf th;
                    ap \<leftarrow> AP_THM eq tm;
                    l \<leftarrow> lhs ap;
                    r \<leftarrow> rhs ap;
                    b1 \<leftarrow> beta_head l;
                    b2 \<leftarrow> beta_head r;
                    s1 \<leftarrow> SYM b1;
                    t1 \<leftarrow> TRANS s1 ap;
                    t2 \<leftarrow> TRANS t1 b2;
                    EQT_ELIM t2 }
           | _ \<Rightarrow> None))"

definition SPECL :: "hterm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "SPECL tms th = foldl (\<lambda>acc t. do { a \<leftarrow> acc; SPEC t a }) (Some th) tms"

definition CONJ :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONJ th1 th2 =
     (let p = concl th1; q = concl th2;
          f = variant (hyp th1 @ hyp th2 @ [p, q]) vf;
          e1 = EQT_INTRO th1; e2 = EQT_INTRO th2
      in do { a1 \<leftarrow> AP_TERM f e1;
              a2 \<leftarrow> MK_COMB a1 e2;
              ab \<leftarrow> ABS f a2;
              unf \<leftarrow> AND_UNFOLD p q;
              su \<leftarrow> SYM unf;
              EQ_MP su ab })"

definition conj_sel :: "bool \<Rightarrow> hterm" where
  "conj_sel first = Abs vp (Abs vq (if first then vp else vq))"

definition CONJUNCT_GEN :: "bool \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONJUNCT_GEN first th =
     do { (p, q) \<leftarrow> dest_conj (concl th);
          unf \<leftarrow> AND_UNFOLD p q;
          th1 \<leftarrow> EQ_MP unf th;
          ap \<leftarrow> AP_THM th1 (conj_sel first);
          l \<leftarrow> lhs ap;
          r \<leftarrow> rhs ap;
          lnf \<leftarrow> beta_head l;
          rnf \<leftarrow> beta_head r;
          s \<leftarrow> SYM lnf;
          t1 \<leftarrow> TRANS s ap;
          t2 \<leftarrow> TRANS t1 rnf;
          EQT_ELIM t2 }"

definition CONJUNCT1 :: "hthm \<Rightarrow> hthm option" where "CONJUNCT1 = CONJUNCT_GEN True"
definition CONJUNCT2 :: "hthm \<Rightarrow> hthm option" where "CONJUNCT2 = CONJUNCT_GEN False"

definition MP :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "MP th1 th2 =
     do { (p, q) \<leftarrow> dest_imp (concl th1);
          unf \<leftarrow> IMP_UNFOLD p q;
          e \<leftarrow> EQ_MP unf th1;
          se \<leftarrow> SYM e;
          pq \<leftarrow> EQ_MP se th2;
          CONJUNCT2 pq }"

definition DISCH :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISCH p th =
     (let q = concl th in
      do { ap \<leftarrow> ASSUME p;
           c1 \<leftarrow> CONJ ap th;
           apq \<leftarrow> ASSUME (mk_conj p q);
           c2 \<leftarrow> CONJUNCT1 apq;
           let e = DEDUCT_ANTISYM_RULE c1 c2;
           unf \<leftarrow> IMP_UNFOLD p q;
           su \<leftarrow> SYM unf;
           EQ_MP su e })"

definition UNDISCH :: "hthm \<Rightarrow> hthm option" where
  "UNDISCH th =
     do { (p, _) \<leftarrow> dest_imp (concl th);
          ap \<leftarrow> ASSUME p;
          MP th ap }"

definition CONTR :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONTR tm th =
     (if concl th = F_tm
      then do { a \<leftarrow> EQ_MP F_DEF th; SPEC tm a } else None)"

definition NOT_ELIM :: "hthm \<Rightarrow> hthm option" where
  "NOT_ELIM th = do { p \<leftarrow> dest_neg (concl th); u \<leftarrow> NOT_UNFOLD p; EQ_MP u th }"

definition NOT_INTRO :: "hthm \<Rightarrow> hthm option" where
  "NOT_INTRO th =
     do { (p, _) \<leftarrow> dest_imp (concl th);
          u \<leftarrow> NOT_UNFOLD p;
          su \<leftarrow> SYM u;
          EQ_MP su th }"

definition DISJ_GEN :: "bool \<Rightarrow> hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISJ_GEN left other th =
     (let c = concl th;
          p = (if left then c else other); q = (if left then other else c);
          r = variant (hyp th @ [p, q]) vr
      in do { unf \<leftarrow> OR_UNFOLD p q;
              su \<leftarrow> SYM unf;
              h1 \<leftarrow> ASSUME (mk_imp p r);
              h2 \<leftarrow> ASSUME (mk_imp q r);
              m \<leftarrow> MP (if left then h1 else h2) th;
              d2 \<leftarrow> DISCH (mk_imp q r) m;
              d1 \<leftarrow> DISCH (mk_imp p r) d2;
              g \<leftarrow> GEN r d1;
              EQ_MP su g })"

definition DISJ1 :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where "DISJ1 th q = DISJ_GEN True q th"
definition DISJ2 :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where "DISJ2 p th = DISJ_GEN False p th"

definition DISJ_CASES :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "DISJ_CASES th0 th1 th2 =
     do { (p, q) \<leftarrow> dest_disj (concl th0);
          let c = concl th1;
          unf \<leftarrow> OR_UNFOLD p q;
          t \<leftarrow> EQ_MP unf th0;
          s \<leftarrow> SPEC c t;
          d1 \<leftarrow> DISCH p th1;
          m1 \<leftarrow> MP s d1;
          d2 \<leftarrow> DISCH q th2;
          MP m1 d2 }"

definition EXCLUDED_MIDDLE :: "hterm \<Rightarrow> hthm option" where
  "EXCLUDED_MIDDLE p =
     do { bc \<leftarrow> SPEC p BOOL_CASES_AX;
          let eT = safe_mk_eq p T_tm;
          let eF = safe_mk_eq p F_tm;
          aT \<leftarrow> ASSUME eT;
          pT \<leftarrow> EQT_ELIM aT;
          c1 \<leftarrow> DISJ1 pT (mk_not p);
          aF \<leftarrow> ASSUME eF;
          ap \<leftarrow> ASSUME p;
          fF \<leftarrow> EQ_MP aF ap;
          dd \<leftarrow> DISCH p fF;
          np \<leftarrow> NOT_INTRO dd;
          c2 \<leftarrow> DISJ2 p np;
          DISJ_CASES bc c1 c2 }"

definition CCONTR :: "hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CCONTR p th =
     do { em \<leftarrow> EXCLUDED_MIDDLE p;
          ap \<leftarrow> ASSUME p;
          c \<leftarrow> CONTR p th;
          DISJ_CASES em ap c }"

definition IMP_ANTISYM_RULE :: "hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "IMP_ANTISYM_RULE th1 th2 =
     do { u1 \<leftarrow> UNDISCH th1; u2 \<leftarrow> UNDISCH th2; Some (DEDUCT_ANTISYM_RULE u2 u1) }"

definition EQF_INTRO :: "hthm \<Rightarrow> hthm option" where
  "EQF_INTRO th =
     do { n \<leftarrow> NOT_ELIM th;
          p \<leftarrow> dest_neg (concl th);
          ap \<leftarrow> ASSUME p;
          f \<leftarrow> MP n ap;
          aF \<leftarrow> ASSUME F_tm;
          pc \<leftarrow> CONTR p aF;
          Some (DEDUCT_ANTISYM_RULE pc f) }"

definition EQF_ELIM :: "hthm \<Rightarrow> hthm option" where
  "EQF_ELIM th =
     do { (p, _) \<leftarrow> dest_eq (concl th);
          ap \<leftarrow> ASSUME p;
          f \<leftarrow> EQ_MP th ap;
          d \<leftarrow> DISCH p f;
          NOT_INTRO d }"


section \<open>Ground evaluation and a propositional tautology prover\<close>

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
        Some True \<Rightarrow> do { x \<leftarrow> pt tm; Some (EQT_INTRO x) }
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

definition TAUT :: "hterm \<Rightarrow> hthm option" where
  "TAUT t = taut_n (Suc (length (bool_atoms t))) t"

section \<open>Matching and rewriting\<close>

type_synonym tyenv = "(hol_type \<times> hol_type) list"
type_synonym tmenv = "(hterm \<times> hterm) list"

fun match_ty :: "hol_type \<Rightarrow> hol_type \<Rightarrow> tyenv \<Rightarrow> tyenv option"
and match_tys :: "hol_type list \<Rightarrow> hol_type list \<Rightarrow> tyenv \<Rightarrow> tyenv option" where
  "match_ty (Tyvar v) ty env =
     (case find (\<lambda>p. snd p = Tyvar v) env of
        Some p \<Rightarrow> if fst p = ty then Some env else None
      | None \<Rightarrow> Some ((ty, Tyvar v) # env))"
| "match_ty (Tyapp c as) (Tyapp c' bs) env = (if c = c' then match_tys as bs env else None)"
| "match_ty (Tyapp _ _) (Tyvar _) env = None"
| "match_tys [] [] env = Some env"
| "match_tys (a # as) (b # bs) env =
     (case match_ty a b env of None \<Rightarrow> None | Some e \<Rightarrow> match_tys as bs e)"
| "match_tys _ _ env = None"

fun match_tm :: "hterm \<Rightarrow> hterm \<Rightarrow> tyenv \<times> tmenv \<Rightarrow> (tyenv \<times> tmenv) option" where
  "match_tm (Var n ty) tm (tye, tme) =
     (case match_ty ty (type_of tm) tye of
        None \<Rightarrow> None
      | Some tye' \<Rightarrow>
          (case find (\<lambda>p. snd p = Var n ty) tme of
             Some p \<Rightarrow> if aconv (fst p) tm then Some (tye', tme) else None
           | None \<Rightarrow> Some (tye', (tm, Var n ty) # tme)))"
| "match_tm (Const n ty) tm (tye, tme) =
     (case tm of
        Const n' ty' \<Rightarrow>
          (if n = n' then (case match_ty ty ty' tye of Some t \<Rightarrow> Some (t, tme) | None \<Rightarrow> None) else None)
      | _ \<Rightarrow> None)"
| "match_tm (Comb s t) tm env =
     (case tm of
        Comb s' t' \<Rightarrow> (case match_tm s s' env of None \<Rightarrow> None | Some e \<Rightarrow> match_tm t t' e)
      | _ \<Rightarrow> None)"
| "match_tm (Abs v b) tm env = (if aconv (Abs v b) tm then Some env else None)"

definition REWR_CONV :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "REWR_CONV th tm =
     do { (l, _) \<leftarrow> dest_eq (concl th);
          (tye, tme) \<leftarrow> match_tm l tm ([], []);
          th1 \<leftarrow> INST_TYPE tye th;
          let theta = map (\<lambda>p. (fst p, (case snd p of Var n ty \<Rightarrow> Var n (type_subst tye ty) | v \<Rightarrow> v))) tme;
          th2 \<leftarrow> INST theta th1;
          l2 \<leftarrow> lhs th2;
          (if aconv l2 tm then Some th2 else None) }"

text \<open>Rewrite rules are theorems @{text "\<turnstile> l = r"}, possibly conditional
  (@{text "\<turnstile> c \<Longrightarrow> l = r"}, nested for several conditions).  A rule is permutative if its two
  sides match each other; such rules only fire when they decrease the term order.\<close>

definition is_perm_rule :: "hthm \<Rightarrow> bool" where
  "is_perm_rule th =
     (case dest_eq (concl th) of
        Some (l, r) \<Rightarrow> match_tm l r ([], []) \<noteq> None \<and> match_tm r l ([], []) \<noteq> None
      | None \<Rightarrow> False)"

fun strip_conds :: "hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_conds (Comb (Comb (Const n ty) c) r) =
     (if n = ''IMP'' then (case strip_conds r of (cs, e) \<Rightarrow> (c # cs, e))
      else ([], Comb (Comb (Const n ty) c) r))"
| "strip_conds tm = ([], tm)"

text \<open>A rewrite step at the root of a term.  Conditions are discharged by the supplied
  solver, which maps a proposition @{text c} to a theorem @{text "\<turnstile> c"}.\<close>

definition rewr_root :: "(hterm \<Rightarrow> hthm option) \<Rightarrow> hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "rewr_root solve th tm =
     (case strip_conds (concl th) of
        ([], _) \<Rightarrow>
          do { th2 \<leftarrow> REWR_CONV th tm;
               (l, r) \<leftarrow> dest_eq (concl th2);
               (if is_perm_rule th \<and> alphaorder r l \<noteq> CLt then None else Some th2) }
      | (cs, eqn) \<Rightarrow>
          do { (l, _) \<leftarrow> dest_eq eqn;
               (tye, tme) \<leftarrow> match_tm l tm ([], []);
               th1 \<leftarrow> INST_TYPE tye th;
               let theta = map (\<lambda>p. (fst p, (case snd p of Var n ty \<Rightarrow> Var n (type_subst tye ty) | v \<Rightarrow> v))) tme;
               th2 \<leftarrow> INST theta th1;
               foldl (\<lambda>acc _. do { a \<leftarrow> acc;
                                   (c, _) \<leftarrow> dest_imp (concl a);
                                   pc \<leftarrow> solve c;
                                   MP a pc }) (Some th2) cs })"

definition try_rules :: "(hterm \<Rightarrow> hthm option) \<Rightarrow> hthm list \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "try_rules solve rules tm =
     foldl (\<lambda>acc th. case acc of Some r \<Rightarrow> Some r | None \<Rightarrow> rewr_root solve th tm) None rules"

text \<open>Bottom-up rewriting to a normal form.  @{text "norm k rules tm"} returns a theorem
  @{text "\<turnstile> tm = tm'"} (reflexivity if nothing applies); @{text k} bounds the recursion depth.
  Conditions of conditional rules are solved by normalising them to @{text T}.\<close>

primrec norm :: "nat \<Rightarrow> hthm list \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "norm 0 rules tm = Some (REFL tm)"
| "norm (Suc k) rules tm =
     (let solve = (\<lambda>c. do { e \<leftarrow> norm k rules c;
                            r \<leftarrow> rhs e;
                            (if r = T_tm then EQT_ELIM e else None) })
      in
      do { sub \<leftarrow> (case tm of
                    Comb s t \<Rightarrow> do { th1 \<leftarrow> norm k rules s; th2 \<leftarrow> norm k rules t; MK_COMB th1 th2 }
                  | Abs v b \<Rightarrow> do { th1 \<leftarrow> norm k rules b; ABS v th1 }
                  | _ \<Rightarrow> Some (REFL tm));
           tm' \<leftarrow> rhs sub;
           (case try_rules solve rules tm' of
              None \<Rightarrow> Some sub
            | Some th \<Rightarrow>
                do { tm'' \<leftarrow> rhs th;
                     th3 \<leftarrow> norm k rules tm'';
                     TRANS3 sub th th3 }) })"


section \<open>Term utilities\<close>

fun strip_comb :: "hterm \<Rightarrow> hterm \<times> hterm list" where
  "strip_comb (Comb f x) = (case strip_comb f of (h, args) \<Rightarrow> (h, args @ [x]))"
| "strip_comb tm = (tm, [])"

definition list_mk_comb :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm option" where
  "list_mk_comb h args = foldl (\<lambda>acc a. do { f \<leftarrow> acc; mk_comb f a }) (Some h) args"

primrec dest_disjuncts :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "dest_disjuncts 0 tm = [tm]"
| "dest_disjuncts (Suc n) tm =
     (case dest_disj tm of
        Some (a, b) \<Rightarrow> dest_disjuncts n a @ dest_disjuncts n b
      | None \<Rightarrow> [tm])"

definition disjuncts :: "hterm \<Rightarrow> hterm list" where
  "disjuncts tm = dest_disjuncts (tm_size tm) tm"

definition mk_clause :: "hterm list \<Rightarrow> hterm" where
  "mk_clause lits =
     (case rev lits of
        [] \<Rightarrow> F_tm
      | l # ls \<Rightarrow> foldl (\<lambda>acc a. mk_disj a acc) l ls)"

primrec dest_conjuncts :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "dest_conjuncts 0 tm = [tm]"
| "dest_conjuncts (Suc n) tm =
     (case dest_conj tm of
        Some (a, b) \<Rightarrow> dest_conjuncts n a @ dest_conjuncts n b
      | None \<Rightarrow> [tm])"

definition conjuncts :: "hterm \<Rightarrow> hterm list" where
  "conjuncts tm = dest_conjuncts (tm_size tm) tm"

definition mk_conj_list :: "hterm list \<Rightarrow> hterm" where
  "mk_conj_list ts =
     (case rev ts of
        [] \<Rightarrow> T_tm
      | l # ls \<Rightarrow> foldl (\<lambda>acc a. mk_conj a acc) l ls)"

fun type_of_args :: "hol_type \<Rightarrow> hol_type list" where
  "type_of_args (Tyapp c [a, b]) = (if c = ''fun'' then a # type_of_args b else [])"
| "type_of_args _ = []"

definition CONV_RULE :: "(hterm \<Rightarrow> hthm option) \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "CONV_RULE conv th = do { e \<leftarrow> conv (concl th); EQ_MP e th }"

text \<open>Beta-normalisation of all redexes in a term, with proof.\<close>

primrec beta_all_n :: "nat \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "beta_all_n 0 tm = Some (REFL tm)"
| "beta_all_n (Suc k) tm =
     (do { sub \<leftarrow> (case tm of
                    Comb s t \<Rightarrow> do { a \<leftarrow> beta_all_n k s; b \<leftarrow> beta_all_n k t; MK_COMB a b }
                  | Abs v b \<Rightarrow> do { a \<leftarrow> beta_all_n k b; ABS v a }
                  | _ \<Rightarrow> Some (REFL tm));
           tm' \<leftarrow> rhs sub;
           (case tm' of
              Comb (Abs _ _) _ \<Rightarrow>
                do { b \<leftarrow> BETA_CONV tm'; tm'' \<leftarrow> rhs b; c \<leftarrow> beta_all_n k tm''; TRANS3 sub b c }
            | _ \<Rightarrow> Some sub) })"

definition beta_all :: "hterm \<Rightarrow> hthm option" where "beta_all = beta_all_n 60"

section \<open>Rewrite rules from theorems\<close>

text \<open>HOL Light's @{text mk_rewrites}: strip universal quantifiers, split conjunctions,
  turn @{text "\<not> p"} into @{text "p = F"} and other propositions into @{text "p = T"}.\<close>

primrec mk_rewrites_n :: "nat \<Rightarrow> hthm \<Rightarrow> hthm list" where
  "mk_rewrites_n 0 th = []"
| "mk_rewrites_n (Suc n) th =
     (let c = concl th in
      case dest_forall c of
        Some (v, _) \<Rightarrow> (case SPEC v th of Some th' \<Rightarrow> mk_rewrites_n n th' | None \<Rightarrow> [])
      | None \<Rightarrow>
        (case dest_conj c of
           Some _ \<Rightarrow> (case (CONJUNCT1 th, CONJUNCT2 th) of
                       (Some a, Some b) \<Rightarrow> mk_rewrites_n n a @ mk_rewrites_n n b
                     | _ \<Rightarrow> [])
         | None \<Rightarrow>
           (case dest_imp c of
              Some (hyp_, conc) \<Rightarrow>
                (case dest_eq conc of
                   Some _ \<Rightarrow> [th]
                 | None \<Rightarrow>
                     (case ASSUME hyp_ of
                        Some ah \<Rightarrow>
                          (case MP th ah of
                             Some m \<Rightarrow>
                               (let rs = mk_rewrites_n n m in
                                List.map_filter (\<lambda>r. DISCH hyp_ r) rs)
                           | None \<Rightarrow> [])
                      | None \<Rightarrow> []))
            | None \<Rightarrow>
              (case dest_eq c of
                 Some (l, _) \<Rightarrow> (case l of Var _ _ \<Rightarrow> [] | _ \<Rightarrow> [th])
               | None \<Rightarrow>
                 (case dest_neg c of
                    Some _ \<Rightarrow> (case EQF_INTRO th of Some e \<Rightarrow> [e] | None \<Rightarrow> [])
                  | None \<Rightarrow> [EQT_INTRO th])))))"

definition mk_rewrites :: "hthm \<Rightarrow> hthm list" where
  "mk_rewrites = mk_rewrites_n 12"

definition mk_rewrites_l :: "hthm list \<Rightarrow> hthm list" where
  "mk_rewrites_l ths = concat (map mk_rewrites ths)"

section \<open>Propositional rewrite rules (proved by TAUT)\<close>

definition ptm :: hterm where "ptm = Var ''p'' bool_ty"
definition qtm :: hterm where "qtm = Var ''q'' bool_ty"
definition rtm :: hterm where "rtm = Var ''r'' bool_ty"

definition cnf_rule_tms :: "hterm list" where
  "cnf_rule_tms =
     [ safe_mk_eq (mk_imp ptm qtm) (mk_disj (mk_not ptm) qtm),
       safe_mk_eq (safe_mk_eq ptm qtm) (mk_conj (mk_disj (mk_not ptm) qtm) (mk_disj (mk_not qtm) ptm)),
       safe_mk_eq (mk_not (mk_not ptm)) ptm,
       safe_mk_eq (mk_not (mk_conj ptm qtm)) (mk_disj (mk_not ptm) (mk_not qtm)),
       safe_mk_eq (mk_not (mk_disj ptm qtm)) (mk_conj (mk_not ptm) (mk_not qtm)),
       safe_mk_eq (mk_disj ptm (mk_conj qtm rtm)) (mk_conj (mk_disj ptm qtm) (mk_disj ptm rtm)),
       safe_mk_eq (mk_disj (mk_conj qtm rtm) ptm) (mk_conj (mk_disj qtm ptm) (mk_disj rtm ptm)),
       safe_mk_eq (mk_disj (mk_disj ptm qtm) rtm) (mk_disj ptm (mk_disj qtm rtm)),
       safe_mk_eq (mk_not T_tm) F_tm,
       safe_mk_eq (mk_not F_tm) T_tm,
       safe_mk_eq (mk_disj T_tm ptm) T_tm,
       safe_mk_eq (mk_disj ptm T_tm) T_tm,
       safe_mk_eq (mk_disj F_tm ptm) ptm,
       safe_mk_eq (mk_disj ptm F_tm) ptm,
       safe_mk_eq (mk_conj T_tm ptm) ptm,
       safe_mk_eq (mk_conj ptm T_tm) ptm,
       safe_mk_eq (mk_conj F_tm ptm) F_tm,
       safe_mk_eq (mk_conj ptm F_tm) F_tm ]"

definition simp_bool_rule_tms :: "hterm list" where
  "simp_bool_rule_tms =
     [ safe_mk_eq (mk_not (mk_not ptm)) ptm,
       safe_mk_eq (mk_not T_tm) F_tm,
       safe_mk_eq (mk_not F_tm) T_tm,
       safe_mk_eq (mk_disj T_tm ptm) T_tm,
       safe_mk_eq (mk_disj ptm T_tm) T_tm,
       safe_mk_eq (mk_disj F_tm ptm) ptm,
       safe_mk_eq (mk_disj ptm F_tm) ptm,
       safe_mk_eq (mk_conj T_tm ptm) ptm,
       safe_mk_eq (mk_conj ptm T_tm) ptm,
       safe_mk_eq (mk_conj F_tm ptm) F_tm,
       safe_mk_eq (mk_conj ptm F_tm) F_tm ]"

definition eq_refl_thm :: hthm where
  "eq_refl_thm = EQT_INTRO (REFL (Var ''x'' aty))"

definition cnf_rules :: "hthm list" where
  "cnf_rules = List.map_filter TAUT cnf_rule_tms"

definition simp_bool_rules :: "hthm list" where
  "simp_bool_rules = List.map_filter TAUT simp_bool_rule_tms @ [eq_refl_thm]"

section \<open>Clausal form (conjunction of clauses)\<close>

definition cnf_conv :: "hterm \<Rightarrow> hthm option" where
  "cnf_conv tm = norm 120 cnf_rules tm"

end
