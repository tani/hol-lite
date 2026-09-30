theory HOL_Lite_Step_Operators_Core
  imports HOL_Lite_Finite_Type_Instantiation HOL_Lite_Bounded_Derivation "HOL-Library.FuncSet"
begin

section \<open>Finite one-step forward operators for the clipped rules\<close>

text \<open>
  This theory gives finite, set-theoretic one-step operators for @{text "bderiv N r"} at fixed
  finite @{term N} and @{term r}. The union theorem \<open>derivable_iff_bderiv\<close> in
  \<open>HOL_Lite_Bounded_Derivation\<close>
  does not itself decide derivability at any fixed bound.

  For each of the ten rules of @{text bderiv} (excluding the inapplicable @{text inst} rule),
  the operators enumerate bounded premises, names and types as finite sets. Type instantiation
  uses the finite representatives from \<open>HOL_Lite_Finite_Type_Instantiation\<close>. The rule-step
  correctness theorems
  equate each output with the conclusions admitted by its rule within @{term "Sequent_r N \<Sigma> r"}.
  These set expressions are not executable list enumerators.
\<close>

context hol_lite
begin

subsection \<open>Recognising equations\<close>

text \<open>
  @{const mk_eq} is injective, but the rules @{text trans}, @{text mk_comb}, @{text eq_mp} need
  to pattern-match an arbitrary premise conclusion against the @{term "mk_eq \<tau> s t"} shape. This
  is exactly the executable, syntax-directed inverse of @{const mk_eq}.
\<close>

definition dest_eq :: "tm \<Rightarrow> (ty \<times> tm \<times> tm) option" where
  "dest_eq c = (case c of
     App (App (Cst eq (TyApp fn [\<tau>, TyApp fn2 [\<tau>', TyApp bn []]])) s) u \<Rightarrow>
        if eq = ''='' \<and> fn = ''fun'' \<and> fn2 = ''fun'' \<and> \<tau>' = \<tau> \<and> bn = ''bool'' then Some (\<tau>,s,u) else None
   | _ \<Rightarrow> None)"

lemma dest_eq_mk_eq [simp]: "dest_eq (mk_eq \<tau> s t) = Some (\<tau>, s, t)"
  unfolding dest_eq_def mk_eq_def by simp

lemma dest_eq_sound: "dest_eq c = Some (\<tau>, s, t) \<Longrightarrow> c = mk_eq \<tau> s t"
  unfolding dest_eq_def mk_eq_def
  by (auto split: tm.splits ty.splits list.splits if_splits)

subsection \<open>Downward closure of the bounded region under immediate subterms\<close>

text \<open>
  Whenever a compound term built by @{const mk_eq}, @{const App}, @{const Fv} or @{const Abs}
  lies in @{term "Tm N \<Sigma> r"}, so do its immediate constituents: @{const wf_tm} recurses through
  exactly these constructors, and @{const tm_size}/@{const ty_size} strictly increase, so the
  same bound @{term r} (and @{term N}) already suffices for the parts. These four facts are the
  engine behind every completeness (@{text "\<supseteq>"}) proof below: the enumeration only ever needs to
  search inside the ALREADY-BOUNDED input, never outside it.
\<close>

lemma Tm_mk_eq_argD:
  assumes "mk_eq \<tau> s t \<in> Tm N \<Sigma> r"
  shows "s \<in> Tm N \<Sigma> r" and "t \<in> Tm N \<Sigma> r" and "\<tau> \<in> Ty N \<Sigma> r"
  using assms
  unfolding mk_eq_def Tm_def Ty_def
  by (auto simp: Ty_def)

lemma Tm_App_argD:
  assumes "App f a \<in> Tm N \<Sigma> r"
  shows "f \<in> Tm N \<Sigma> r" and "a \<in> Tm N \<Sigma> r"
  using assms unfolding Tm_def by auto

lemma Tm_Fv_argD:
  assumes "Fv x \<sigma> \<in> Tm N \<Sigma> r"
  shows "x \<in> N" and "\<sigma> \<in> Ty N \<Sigma> r"
  using assms unfolding Tm_def by auto

lemma Tm_Abs_argD:
  assumes "Abs \<sigma> b \<in> Tm N \<Sigma> r"
  shows "\<sigma> \<in> Ty N \<Sigma> r" and "b \<in> Tm N \<Sigma> r"
  using assms unfolding Tm_def by auto

subsection \<open>\<open>refl\<close>: enumerate @{term "Tm_wt N \<Sigma> r"}\<close>

definition step_refl :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "step_refl N r = (\<Union>t\<in>Tm_wt N \<Sigma> r. case typeof \<Sigma> [] t of
       Some \<tau> \<Rightarrow> (if ({}, mk_eq \<tau> t t) \<in> Sequent_r N \<Sigma> r then {({}, mk_eq \<tau> t t)} else {})
     | None \<Rightarrow> {})"

lemma step_refl_sound: "step_refl N r \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_refl_def by (auto split: option.splits if_splits)

lemma finite_step_refl: "finite N \<Longrightarrow> finite (step_refl N r)"
  using step_refl_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_refl:
  "step_refl N r = {p \<in> Sequent_r N \<Sigma> r. \<exists>t \<tau>. has_type \<Sigma> [] t \<tau> \<and> p = ({}, mk_eq \<tau> t t)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_refl_def
    by (fastforce split: option.splits if_splits simp: typeof_iff_has_type)
next
  show "?R \<subseteq> ?L"
  proof
    fix p assume p: "p \<in> ?R"
    then obtain t \<tau> where ht: "has_type \<Sigma> [] t \<tau>" and peq: "p = ({}, mk_eq \<tau> t t)"
      and mem: "p \<in> Sequent_r N \<Sigma> r" by blast
    from mem peq have cmem: "mk_eq \<tau> t t \<in> Tm_wt N \<Sigma> r" unfolding Sequent_r_def by auto
    from cmem have cmemT: "mk_eq \<tau> t t \<in> Tm N \<Sigma> r" unfolding Tm_wt_def by simp
    from Tm_mk_eq_argD(1)[OF cmemT] have tmemT: "t \<in> Tm N \<Sigma> r" .
    from typeof_complete[OF ht] have tof: "typeof \<Sigma> [] t = Some \<tau>" .
    from tmemT tof have tmem: "t \<in> Tm_wt N \<Sigma> r" unfolding Tm_wt_def by simp
    from tmem tof mem peq show "p \<in> ?L"
      unfolding step_refl_def using tof by (intro UN_I[where a = t]) simp_all
  qed
qed

subsection \<open>\<open>assm\<close>: enumerate @{term "Tm_wt N \<Sigma> r"}\<close>

definition step_assm :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "step_assm N r = (\<Union>p\<in>Tm_wt N \<Sigma> r.
     if typeof \<Sigma> [] p = Some boolT \<and> ({p}, p) \<in> Sequent_r N \<Sigma> r then {({p}, p)} else {})"

lemma step_assm_sound: "step_assm N r \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_assm_def by (auto split: if_splits)

lemma finite_step_assm: "finite N \<Longrightarrow> finite (step_assm N r)"
  using step_assm_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_assm:
  "step_assm N r = {q \<in> Sequent_r N \<Sigma> r. \<exists>p. has_type \<Sigma> [] p boolT \<and> q = ({p}, p)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_assm_def
    by (fastforce split: if_splits simp: typeof_iff_has_type)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain p where hp: "has_type \<Sigma> [] p boolT" and qeq: "q = ({p}, p)"
      and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    from mem qeq have pmem: "p \<in> Tm_wt N \<Sigma> r" unfolding Sequent_r_def by auto
    from typeof_complete[OF hp] have tof: "typeof \<Sigma> [] p = Some boolT" .
    from pmem tof mem qeq show "q \<in> ?L"
      unfolding step_assm_def by (intro UN_I[where a = p]) simp_all
  qed
qed

subsection \<open>\<open>trans\<close>: enumerate pairs of premises\<close>

definition step_trans :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_trans N r S = (\<Union>p1\<in>S. \<Union>p2\<in>S.
     case (dest_eq (snd p1), dest_eq (snd p2)) of
       (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
         if \<tau>' = \<tau> \<and> t' = t \<and> (fst p1 \<union> fst p2, mk_eq \<tau> s u) \<in> Sequent_r N \<Sigma> r
         then {(fst p1 \<union> fst p2, mk_eq \<tau> s u)} else {}
     | _ \<Rightarrow> {})"

lemma step_trans_sound: "step_trans N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_trans_def by (auto split: option.splits if_splits)

lemma finite_step_trans: "finite N \<Longrightarrow> finite (step_trans N r S)"
  using step_trans_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_trans:
  "step_trans N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> \<Delta> \<tau> s t u. (\<Gamma>, mk_eq \<tau> s t) \<in> S \<and> (\<Delta>, mk_eq \<tau> t u) \<in> S
        \<and> q = (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_trans_def
    by (fastforce split: option.splits if_splits dest: dest_eq_sound)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> \<Delta> \<tau> s t u where p1: "(\<Gamma>, mk_eq \<tau> s t) \<in> S" and p2: "(\<Delta>, mk_eq \<tau> t u) \<in> S"
      and qeq: "q = (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)" and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    show "q \<in> ?L"
      unfolding step_trans_def
      using p1 p2 mem qeq
      by (intro UN_I[where a = "(\<Gamma>, mk_eq \<tau> s t)"] UN_I[where a = "(\<Delta>, mk_eq \<tau> t u)"]) simp_all
  qed
qed

subsection \<open>\<open>mk_comb\<close>: enumerate pairs of premises\<close>

definition step_mk_comb :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_mk_comb N r S = (\<Union>p1\<in>S. \<Union>p2\<in>S.
     case (dest_eq (snd p1), dest_eq (snd p2)) of
       (Some (TyApp fn [\<sigma>0,\<tau>], f, g), Some (\<sigma>, a, b)) \<Rightarrow>
         if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
            \<and> (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N \<Sigma> r
         then {(fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b))} else {}
     | _ \<Rightarrow> {})"

lemma step_mk_comb_sound: "step_mk_comb N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_mk_comb_def by (auto split: option.splits if_splits ty.splits list.splits)

lemma finite_step_mk_comb: "finite N \<Longrightarrow> finite (step_mk_comb N r S)"
  using step_mk_comb_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_mk_comb:
  "step_mk_comb N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> \<Delta> \<sigma> \<tau> f g a b. (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) \<in> S \<and> (\<Delta>, mk_eq \<sigma> a b) \<in> S
        \<and> q = (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_mk_comb_def
    by (fastforce split: option.splits if_splits ty.splits list.splits dest: dest_eq_sound)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> \<Delta> \<sigma> \<tau> f g a b where p1: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) \<in> S"
      and p2: "(\<Delta>, mk_eq \<sigma> a b) \<in> S"
      and qeq: "q = (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))" and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    show "q \<in> ?L"
      unfolding step_mk_comb_def
      using p1 p2 mem qeq
      by (intro UN_I[where a = "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g)"] UN_I[where a = "(\<Delta>, mk_eq \<sigma> a b)"])
         simp_all
  qed
qed

subsection \<open>\<open>eq_mp\<close>: enumerate pairs of premises\<close>

definition step_eq_mp :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_eq_mp N r S = (\<Union>p1\<in>S. \<Union>p2\<in>S.
     case dest_eq (snd p1) of
       Some (\<tau>, p, qc) \<Rightarrow>
         if \<tau> = boolT \<and> snd p2 = p \<and> (fst p1 \<union> fst p2, qc) \<in> Sequent_r N \<Sigma> r
         then {(fst p1 \<union> fst p2, qc)} else {}
     | None \<Rightarrow> {})"

lemma step_eq_mp_sound: "step_eq_mp N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_eq_mp_def by (auto split: option.splits if_splits)

lemma finite_step_eq_mp: "finite N \<Longrightarrow> finite (step_eq_mp N r S)"
  using step_eq_mp_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_eq_mp:
  "step_eq_mp N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> \<Delta> p qc. (\<Gamma>, mk_eq boolT p qc) \<in> S \<and> (\<Delta>, p) \<in> S \<and> q = (\<Gamma> \<union> \<Delta>, qc)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_eq_mp_def
    by (fastforce split: option.splits if_splits dest: dest_eq_sound)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> \<Delta> p qc where p1: "(\<Gamma>, mk_eq boolT p qc) \<in> S" and p2: "(\<Delta>, p) \<in> S"
      and qeq: "q = (\<Gamma> \<union> \<Delta>, qc)" and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    show "q \<in> ?L"
      unfolding step_eq_mp_def
      using p1 p2 mem qeq
      by (intro UN_I[where a = "(\<Gamma>, mk_eq boolT p qc)"] UN_I[where a = "(\<Delta>, p)"]) simp_all
  qed
qed

subsection \<open>\<open>deduct_antisym\<close>: enumerate pairs of premises\<close>

definition step_deduct_antisym :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_deduct_antisym N r S = (\<Union>p1\<in>S. \<Union>p2\<in>S.
     if ((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2)) \<in> Sequent_r N \<Sigma> r
     then {((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2))} else {})"

lemma step_deduct_antisym_sound: "step_deduct_antisym N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_deduct_antisym_def by (auto split: if_splits)

lemma finite_step_deduct_antisym: "finite N \<Longrightarrow> finite (step_deduct_antisym N r S)"
  using step_deduct_antisym_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_deduct_antisym:
  "step_deduct_antisym N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> \<Delta> p qc. (\<Gamma>, p) \<in> S \<and> (\<Delta>, qc) \<in> S
        \<and> q = ((\<Gamma> - {qc}) \<union> (\<Delta> - {p}), mk_eq boolT p qc)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_deduct_antisym_def by (fastforce split: if_splits)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> \<Delta> p qc where p1: "(\<Gamma>, p) \<in> S" and p2: "(\<Delta>, qc) \<in> S"
      and qeq: "q = ((\<Gamma> - {qc}) \<union> (\<Delta> - {p}), mk_eq boolT p qc)" and mem: "q \<in> Sequent_r N \<Sigma> r"
      by blast
    show "q \<in> ?L"
      unfolding step_deduct_antisym_def
      using p1 p2 mem qeq
      by (intro UN_I[where a = "(\<Gamma>, p)"] UN_I[where a = "(\<Delta>, qc)"]) simp_all
  qed
qed

subsection \<open>\<open>beta\<close>: enumerate @{term "Tm_wt N \<Sigma> r"} and names @{term N}\<close>

text \<open>
  Enumerating over Abs-headed elements of @{term "Tm_wt N \<Sigma> r"} (rather than separately over
  types and bodies) is what keeps the search finite: the region does not otherwise expose a
  finite set of ``bodies''.
\<close>

definition step_beta :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "step_beta N r = (\<Union>w\<in>Tm_wt N \<Sigma> r. \<Union>x\<in>N.
     case w of
       Abs \<sigma> b \<Rightarrow>
         (case typeof \<Sigma> [] w of
            Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
              if fn = ''fun'' \<and> \<sigma>' = \<sigma>
                 \<and> ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r N \<Sigma> r
              then {({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))} else {}
          | _ \<Rightarrow> {})
     | _ \<Rightarrow> {})"

lemma step_beta_sound: "step_beta N r \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_beta_def by (auto split: tm.splits option.splits ty.splits list.splits if_splits)

lemma finite_step_beta: "finite N \<Longrightarrow> finite (step_beta N r)"
  using step_beta_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_beta:
  "step_beta N r = {q \<in> Sequent_r N \<Sigma> r. \<exists>x \<sigma> b \<tau>. has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)
     \<and> q = ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_beta_def
    apply (auto split: tm.splits option.splits ty.splits list.splits if_splits
           simp: typeof_iff_has_type)
    by (metis has_type.Abs)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain x \<sigma> b \<tau> where ht: "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)"
      and qeq: "q = ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))"
      and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    from mem qeq have cmem: "mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b) \<in> Tm_wt N \<Sigma> r"
      unfolding Sequent_r_def by auto
    from cmem have cmemT: "mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b) \<in> Tm N \<Sigma> r"
      unfolding Tm_wt_def by simp
    from Tm_mk_eq_argD(1)[OF cmemT] have appmem: "App (Abs \<sigma> b) (Fv x \<sigma>) \<in> Tm N \<Sigma> r" .
    from Tm_App_argD[OF appmem] have wmemT: "Abs \<sigma> b \<in> Tm N \<Sigma> r" and fvmemT: "Fv x \<sigma> \<in> Tm N \<Sigma> r" .
    from Tm_Fv_argD(1)[OF fvmemT] have xmem: "x \<in> N" .
    from typeof_complete[OF ht] have tof: "typeof \<Sigma> [] (Abs \<sigma> b) = Some (funT \<sigma> \<tau>)" .
    from wmemT tof have wmem: "Abs \<sigma> b \<in> Tm_wt N \<Sigma> r" unfolding Tm_wt_def by simp
    from wmem xmem tof mem qeq show "q \<in> ?L"
      unfolding step_beta_def
      by (intro UN_I[where a = "Abs \<sigma> b"] UN_I[where a = x]) simp_all
  qed
qed

end

end
