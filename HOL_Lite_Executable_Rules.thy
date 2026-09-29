theory HOL_Lite_Executable_Rules
  imports HOL_Lite_Executable_Enum
begin

section \<open>Executable one-step bounded search\<close>

context hol_lite_axs
begin

definition bounded_seq :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> bool" where
  "bounded_seq ns r p \<longleftrightarrow> fst p \<subseteq> set (enum_tm ns \<Sigma> r) \<and> snd p \<in> set (enum_tm ns \<Sigma> r)"

lemma bounded_seq_iff [simp]:
  "bounded_seq ns r p \<longleftrightarrow> p \<in> Sequent_r (set ns) \<Sigma> r"
  by (cases p) (simp add: bounded_seq_def Sequent_r_def set_enum_tm)

definition exec_refl :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_refl ns r = concat (map (\<lambda>t. case typeof \<Sigma> [] t of
    Some \<tau> \<Rightarrow> (let q = ({}, mk_eq \<tau> t t) in if bounded_seq ns r q then [q] else [])
  | None \<Rightarrow> []) (enum_tm ns \<Sigma> r))"

lemma set_exec_refl: "set (exec_refl ns r) = step_refl (set ns) r"
  proof -
  have per: "\<And>t. set (case typeof \<Sigma> [] t of
      Some \<tau> \<Rightarrow> (let q = ({}, mk_eq \<tau> t t) in if bounded_seq ns r q then [q] else [])
    | None \<Rightarrow> []) = (case typeof \<Sigma> [] t of
      Some \<tau> \<Rightarrow> (if ({}, mk_eq \<tau> t t) \<in> Sequent_r (set ns) \<Sigma> r
                 then {({}, mk_eq \<tau> t t)} else {})
    | None \<Rightarrow> {})"
    by (simp add: Let_def split: option.splits)
  show ?thesis unfolding exec_refl_def step_refl_def
    using per by (simp add: set_enum_tm)
qed

definition exec_assm :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_assm ns r = concat (map (\<lambda>p. if typeof \<Sigma> [] p = Some boolT \<and>
    bounded_seq ns r ({p}, p) then [({p},p)] else []) (enum_tm ns \<Sigma> r))"

lemma set_exec_assm: "set (exec_assm ns r) = step_assm (set ns) r"
  by (auto simp: exec_assm_def step_assm_def set_enum_tm bounded_seq_iff)

definition exec_axiom :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_axiom ns r = concat (map (\<lambda>p. if bounded_seq ns r ({},p)
    then [({},p)] else []) (axs (set ns) r))"

lemma set_exec_axiom: "set (exec_axiom ns r) = step_axiom (set ns) r"
  by (auto simp: exec_axiom_def step_axiom_def bounded_seq_iff)

definition scan_pair :: "name list \<Rightarrow> nat \<Rightarrow>
  ((tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option) \<Rightarrow>
  (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "scan_pair ns r f S = concat (map (\<lambda>p1. concat (map (\<lambda>p2. case f p1 p2 of
    None \<Rightarrow> [] | Some q \<Rightarrow> if bounded_seq ns r q then [q] else []) S)) S)"

lemma set_concat_map: "set (concat (map g xs)) = (\<Union>x\<in>set xs. set (g x))"
  by (induction xs) auto

lemma set_scan_pair:
  "set (scan_pair ns r f S) = (\<Union>p1\<in>set S. \<Union>p2\<in>set S.
    case f p1 p2 of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
  proof -
  have per: "\<And>p1 p2. set (case f p1 p2 of None \<Rightarrow> []
     | Some q \<Rightarrow> if bounded_seq ns r q then [q] else []) =
     (case f p1 p2 of None \<Rightarrow> {}
     | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
  proof -
    fix p1 p2
    show "set (case f p1 p2 of None \<Rightarrow> []
       | Some q \<Rightarrow> if bounded_seq ns r q then [q] else []) =
       (case f p1 p2 of None \<Rightarrow> {}
       | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
      by (cases "f p1 p2") simp_all
  qed
  show ?thesis unfolding scan_pair_def
    using per by (simp only: set_concat_map)
qed

definition exec_trans :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_trans ns r S = scan_pair ns r (\<lambda>p1 p2.
    case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
    | _ \<Rightarrow> None) S"

lemma set_exec_trans: "set (exec_trans ns r S) = step_trans (set ns) r (set S)"
  proof -
  have per: "\<And>p1 p2. (case (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
      | _ \<Rightarrow> None) of
      None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t \<and>
           (fst p1 \<union> fst p2, mk_eq \<tau> s u) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2, mk_eq \<tau> s u)} else {}
      | _ \<Rightarrow> {})"
    by (simp split: option.splits prod.splits if_splits)
  show ?thesis unfolding exec_trans_def set_scan_pair step_trans_def
    using per by simp
qed

lemma case_guarded_result [simp]:
  "(case (if P then Some q else None) of None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}) =
     (if P \<and> q \<in> Q then {q} else {})"
  by simp

lemma case_option_result [simp]:
  "(case (case z of None \<Rightarrow> None | Some y \<Rightarrow> f y) of
       None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}) =
    (case z of None \<Rightarrow> {} | Some y \<Rightarrow>
      (case f y of None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}))"
  by (cases z) simp_all

definition exec_mk_comb :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_mk_comb ns r S = scan_pair ns r (\<lambda>p1 p2.
    case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
        then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
    | _ \<Rightarrow> None) S"

lemma set_exec_mk_comb: "set (exec_mk_comb ns r S) = step_mk_comb (set ns) r (set S)"
  proof -
  have per: "\<And>p1 p2. (case (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
        then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
    | _ \<Rightarrow> None) of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma> \<and>
           (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b))} else {}
    | _ \<Rightarrow> {})"
    by (simp split: option.splits prod.splits ty.splits list.splits if_splits)
  show ?thesis unfolding exec_mk_comb_def set_scan_pair step_mk_comb_def
    using per by simp
qed

definition exec_eq_mp :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_eq_mp ns r S = scan_pair ns r (\<lambda>p1 p2.
    case dest_eq (snd p1) of
      Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p
        then Some (fst p1 \<union> fst p2,q) else None
    | None \<Rightarrow> None) S"

lemma set_exec_eq_mp: "set (exec_eq_mp ns r S) = step_eq_mp (set ns) r (set S)"
  proof -
  have per: "\<And>p1 p2. (case (case dest_eq (snd p1) of
    Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p then Some (fst p1 \<union> fst p2,q) else None
    | None \<Rightarrow> None) of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case dest_eq (snd p1) of
      Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p \<and>
        (fst p1 \<union> fst p2,q) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2,q)} else {}
    | None \<Rightarrow> {})"
    by (simp split: option.splits prod.splits if_splits)
  show ?thesis unfolding exec_eq_mp_def set_scan_pair step_eq_mp_def
    using per by simp
qed

definition exec_deduct_antisym :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_deduct_antisym ns r S = scan_pair ns r (\<lambda>p1 p2.
    Some ((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2))) S"

lemma set_exec_deduct_antisym:
  "set (exec_deduct_antisym ns r S) = step_deduct_antisym (set ns) r (set S)"
  unfolding exec_deduct_antisym_def set_scan_pair step_deduct_antisym_def by simp

definition exec_beta :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_beta ns r = concat (map (\<lambda>w. concat (map (\<lambda>x.
    case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (let q = ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) in
         if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and> bounded_seq ns r q then [q] else [])
      | _ \<Rightarrow> [])
    | _ \<Rightarrow> []) ns)) (enum_tm ns \<Sigma> r))"

lemma set_exec_beta: "set (exec_beta ns r) = step_beta (set ns) r"
  proof -
  have per: "\<And>w x. set (case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (let q = ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) in
         if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and> bounded_seq ns r q then [q] else [])
      | _ \<Rightarrow> []) | _ \<Rightarrow> []) =
    (case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and>
          ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r (set ns) \<Sigma> r
         then {({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))} else {})
      | _ \<Rightarrow> {}) | _ \<Rightarrow> {})"
    by (simp add: Let_def split: tm.splits option.splits ty.splits list.splits if_splits)
  show ?thesis unfolding exec_beta_def step_beta_def
    using per by (simp add: set_enum_tm set_concat_map)
qed

definition exec_abs :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_abs ns r S = concat (map (\<lambda>p1. concat (map (\<lambda>\<sigma>. concat (map (\<lambda>x.
    case dest_eq (snd p1) of
      Some (\<tau>,s,t) \<Rightarrow>
        (let q = (fst p1, mk_eq (funT \<sigma> \<tau>)
           (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) in
         if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> bounded_seq ns r q then [q] else [])
    | None \<Rightarrow> []) (fresh_name (set ns) # ns))) (enum_ty ns \<Sigma> r))) S)"

lemma set_exec_abs: "set (exec_abs ns r S) = step_abs (set ns) r (set S)"
  proof -
  have per: "\<And>p1 \<sigma> x. set (case dest_eq (snd p1) of
      Some (\<tau>,s,t) \<Rightarrow>
        (let q = (fst p1, mk_eq (funT \<sigma> \<tau>)
           (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) in
         if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> bounded_seq ns r q then [q] else [])
    | None \<Rightarrow> []) =
    (case dest_eq (snd p1) of Some (\<tau>,s,t) \<Rightarrow>
       (if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and>
          (fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s))
            (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s))
            (Abs \<sigma> (abs_fv 0 x \<sigma> t)))} else {})
    | None \<Rightarrow> {})"
    by (simp add: Let_def split: option.splits)
  show ?thesis unfolding exec_abs_def step_abs_def
    using per by (simp add: set_enum_ty set_concat_map)
qed

fun inst_envs :: "name list \<Rightarrow> ty list \<Rightarrow> (name \<times> ty) list list" where
  "inst_envs [] tys = [[]]"
| "inst_envs (v # vs) tys = concat (map (\<lambda>\<tau>.
     map (Cons (v,\<tau>)) (inst_envs vs tys)) tys)"

lemma set_inst_envs:
  "set (inst_envs vs tys) = {e. map fst e = vs \<and> set (map snd e) \<subseteq> set tys}"
  proof (induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  show ?case
  proof (rule set_eqI)
    fix e
    show "e \<in> set (inst_envs (a # vs) tys) \<longleftrightarrow>
      e \<in> {e. map fst e = a # vs \<and> set (map snd e) \<subseteq> set tys}"
    proof (cases e)
      case Nil
      then show ?thesis by auto
    next
      case (Cons h tail)
      obtain v \<tau> where h: "h = (v,\<tau>)" by (cases h) auto
      show ?thesis using Cons.IH
        by (auto simp: Cons h image_iff)
    qed
  qed
qed

lemma map_of_range: "map_of e a = Some t \<Longrightarrow> t \<in> set (map snd e)"
  by (induction e) (auto split: if_splits)

lemma map_of_mapped_distinct:
  "distinct vs \<Longrightarrow> map_of (map (\<lambda>v. (v, f v)) vs) a =
    (if a \<in> set vs then Some (f a) else None)"
  by (induction vs) auto

lemma inst_envs_PiE:
  assumes distinct: "distinct vs" and vs: "set vs = V"
  shows "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)} =
         {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}"
proof (rule equalityI)
  show "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)} \<subseteq>
         {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}"
  proof
    fix \<theta> assume "\<theta> \<in> {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}"
    then obtain e where e: "e \<in> set (inst_envs vs tys)"
      and \<theta>: "\<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)" by blast
    have dom: "map fst e = vs" and ran: "set (map snd e) \<subseteq> set tys"
      using e by (auto simp: set_inst_envs)
    have lookup_iff: "\<And>a. map_of e a = None \<longleftrightarrow> a \<notin> V"
      using dom vs by (metis map_of_eq_None_iff set_map)
    let ?f = "restrict (\<lambda>a. the (map_of e a)) V"
    have range: "\<And>a. a \<in> V \<Longrightarrow> the (map_of e a) \<in> set tys"
    proof -
      fix a assume "a \<in> V"
      then have "map_of e a \<noteq> None" using lookup_iff by blast
      then obtain t where hit: "map_of e a = Some t" by (cases "map_of e a") auto
      from map_of_range[OF hit] ran hit show "the (map_of e a) \<in> set tys" by auto
    qed
    have f: "?f \<in> PiE V (\<lambda>_. set tys)"
      using range by (auto intro!: PiE_I)
    have "\<theta> = (\<lambda>a. if a \<in> V then ?f a else boolT)"
    proof (rule ext)
      fix a
      show "\<theta> a = (if a \<in> V then ?f a else boolT)"
      proof (cases "a \<in> V")
        case True
        with lookup_iff obtain t where "map_of e a = Some t"
          by (cases "map_of e a") auto
        with True \<theta> show ?thesis by (simp add: restrict_apply)
      next
        case False
        then have "map_of e a = None" using lookup_iff by blast
        with False \<theta> show ?thesis by simp
      qed
    qed
    with f show "\<theta> \<in> {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}" by blast
  qed
next
  show "{(\<lambda>a. if a \<in> V then f a else boolT) |f. f \<in> PiE V (\<lambda>_. set tys)} \<subseteq>
        {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}"
  proof
    fix \<theta> assume "\<theta> \<in> {(\<lambda>a. if a \<in> V then f a else boolT) |f. f \<in> PiE V (\<lambda>_. set tys)}"
    then obtain f where f: "f \<in> PiE V (\<lambda>_. set tys)"
      and \<theta>: "\<theta> = (\<lambda>a. if a \<in> V then f a else boolT)" by blast
    let ?e = "map (\<lambda>v. (v,f v)) vs"
    have e: "?e \<in> set (inst_envs vs tys)"
      using f vs by (auto simp: set_inst_envs PiE_iff o_def)
    have "\<theta> = (\<lambda>a. case map_of ?e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)"
      by (simp add: \<theta> vs map_of_mapped_distinct[OF distinct] fun_eq_iff)
    with e show "\<theta> \<in> {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}" by blast
  qed
qed

definition inst_vars :: "(tm set \<times> tm) \<Rightarrow> name set" where
  "inst_vars p = tm_tyvars (snd p) \<union> (\<Union>t\<in>fst p. tm_tyvars t)"

fun tyvar_list :: "ty \<Rightarrow> name list" where
  "tyvar_list (TyVar a) = [a]"
| "tyvar_list (TyApp c ts) = concat (map tyvar_list ts)"

fun tm_tyvar_list :: "tm \<Rightarrow> name list" where
  "tm_tyvar_list (Fv x \<tau>) = tyvar_list \<tau>"
| "tm_tyvar_list (Bv i) = []"
| "tm_tyvar_list (Cst c \<tau>) = tyvar_list \<tau>"
| "tm_tyvar_list (App f a) = tm_tyvar_list f @ tm_tyvar_list a"
| "tm_tyvar_list (Abs \<tau> b) = tyvar_list \<tau> @ tm_tyvar_list b"

lemma set_tyvar_list [simp]: "set (tyvar_list \<tau>) = ty_tyvars \<tau>"
  by (induction \<tau> rule: ty.induct) auto

lemma set_tm_tyvar_list [simp]: "set (tm_tyvar_list t) = tm_tyvars t"
  by (induction t rule: tm.induct) auto

definition inst_var_list :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> name list" where
  "inst_var_list ns r p = remdups (tm_tyvar_list (snd p) @
    concat (map tm_tyvar_list (filter (\<lambda>t. t \<in> fst p) (enum_tm ns \<Sigma> r))))"

lemma set_inst_var_list:
  "p \<in> Sequent_r (set ns) \<Sigma> r \<Longrightarrow> set (inst_var_list ns r p) = inst_vars p"
  by (auto simp: inst_var_list_def inst_vars_def Sequent_r_def set_enum_tm)

lemma distinct_inst_var_list [simp]: "distinct (inst_var_list ns r p)"
  by (simp add: inst_var_list_def)

definition exec_inst_type :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_inst_type ns r S = concat (map (\<lambda>p1.
    concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))
      in if bounded_seq ns r q then [q] else [])
      (inst_envs (inst_var_list ns r p1) (enum_ty ns \<Sigma> r)))) S)"

lemma set_exec_inst_type:
  assumes sub: "set S \<subseteq> Sequent_r (set ns) \<Sigma> r"
  shows "set (exec_inst_type ns r S) = step_inst_type (set ns) r (set S)"
proof -
  have per: "\<And>p. p \<in> set S \<Longrightarrow>
    set (concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if bounded_seq ns r q then [q] else [])
      (inst_envs (inst_var_list ns r p) (enum_ty ns \<Sigma> r)))) =
    (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
      let \<theta> = (\<lambda>a. if a \<in> inst_vars p then f a else boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
  proof -
    fix p assume p: "p \<in> set S"
    have var: "set (inst_var_list ns r p) = inst_vars p"
      using p sub set_inst_var_list by blast
    have env_eq:
      "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
           e \<in> set (inst_envs (inst_var_list ns r p) (enum_ty ns \<Sigma> r))} =
       {(\<lambda>a. if a \<in> inst_vars p then f a else boolT) |f.
           f \<in> PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r)}"
      using inst_envs_PiE[OF distinct_inst_var_list var, of "enum_ty ns \<Sigma> r"]
      by (simp add: set_enum_ty)
    have idx: "\<And>F. (\<Union>e\<in>set (inst_envs (inst_var_list ns r p) (enum_ty ns \<Sigma> r)).
       F (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)) =
       (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
       F (\<lambda>a. if a \<in> inst_vars p then f a else boolT))"
    proof -
      fix F
      let ?E = "set (inst_envs (inst_var_list ns r p) (enum_ty ns \<Sigma> r))"
      let ?P = "PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r)"
      let ?g = "\<lambda>e a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT"
      let ?h = "\<lambda>f a. if a \<in> inst_vars p then f a else boolT"
      have equal: "?g ` ?E = ?h ` ?P" using env_eq by auto
      have "(\<Union>e\<in>?E. F (?g e)) = (\<Union>\<theta>\<in>?g ` ?E. F \<theta>)" by auto
      also have "... = (\<Union>\<theta>\<in>?h ` ?P. F \<theta>)" using equal by simp
      also have "... = (\<Union>f\<in>?P. F (?h f))" by auto
      finally show "(\<Union>e\<in>?E. F (?g e)) = (\<Union>f\<in>?P. F (?h f))" .
    qed
    show "set (concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if bounded_seq ns r q then [q] else [])
      (inst_envs (inst_var_list ns r p) (enum_ty ns \<Sigma> r)))) =
      (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
      let \<theta> = (\<lambda>a. if a \<in> inst_vars p then f a else boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
      using idx[of "\<lambda>\<theta>. let q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
        in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}"]
      by (simp add: set_concat_map Let_def)
  qed
  show ?thesis unfolding exec_inst_type_def step_inst_type_def inst_vars_def
    using per by (simp add: set_concat_map Let_def inst_vars_def)
qed

definition exec_step :: "name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_step ns r S = remdups
    (exec_refl ns r @ exec_assm ns r @ exec_beta ns r @ exec_axiom ns r @
     exec_trans ns r S @ exec_mk_comb ns r S @ exec_abs ns r S @
     exec_eq_mp ns r S @ exec_deduct_antisym ns r S @ exec_inst_type ns r S)"

lemma set_exec_step:
  "set S \<subseteq> Sequent_r (set ns) \<Sigma> r \<Longrightarrow>
   set (exec_step ns r S) = step_r (set ns) r (set S)"
  unfolding exec_step_def step_r_def
  by (simp add: set_exec_refl set_exec_assm set_exec_beta set_exec_axiom
      set_exec_trans set_exec_mk_comb set_exec_abs set_exec_eq_mp
      set_exec_deduct_antisym set_exec_inst_type Un_assoc)

end
end
