theory HOL_Lite_L7
  imports HOL_Lite_L3 HOL_Lite_L5 "HOL-Library.FuncSet"
begin

section \<open>Finite one-step forward operators for the clipped rules\<close>

text \<open>
  This theory gives finite, set-theoretic one-step operators for @{text "bderiv N r"} at fixed
  finite @{term N} and @{term r}. The union theorem \<open>derivable_iff_bderiv\<close> in \<open>HOL_Lite_L5\<close>
  does not itself decide derivability at any fixed bound.

  For each of the ten rules of @{text bderiv} (excluding the inapplicable @{text inst} rule),
  the operators enumerate bounded premises, names and types as finite sets. Type instantiation
  uses the finite representatives from \<open>HOL_Lite_L3\<close>. The rule-step correctness theorems
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

subsection \<open>\<open>abs\<close>: enumerate types @{term "Ty N \<Sigma> r"} and names @{term N} plus one fresh name\<close>


lemma exists_fresh_name: "finite (N :: name set) \<Longrightarrow> \<exists>x. x \<notin> N"
  using ex_new_if_finite[OF infinite_UNIV_listI, of N]
  by simp

definition fresh_name :: "name set \<Rightarrow> name" where
  "fresh_name N = replicate (Suc (Max (insert 0 (length ` N)))) (CHR ''x'')"

lemma fresh_name_not_mem: "finite N \<Longrightarrow> fresh_name N \<notin> N"
proof
  assume fin: "finite N" and mem: "fresh_name N \<in> N"
  have le: "length (fresh_name N) \<le> Max (insert 0 (length ` N))"
    using Max_ge[of "insert 0 (length ` N)" "length (fresh_name N)"] fin mem by auto
  show False using le by (simp add: fresh_name_def)
qed

lemma abs_fv_id: "(x, \<sigma>) \<notin> fvs t \<Longrightarrow> abs_fv k x \<sigma> t = t"
proof (induction t arbitrary: k)
  case (Fv y \<tau>)
  then show ?case by auto
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  then show ?case by simp
next
  case (App f a)
  then show ?case by simp
next
  case (Abs \<tau> b)
  then show ?case by simp
qed

lemma Tm_fvs_name_mem: "t \<in> Tm N \<Sigma> r \<Longrightarrow> (x, \<sigma>) \<in> fvs t \<Longrightarrow> x \<in> N"
proof (induction t arbitrary: r rule: tm.induct)
  case (Fv y \<tau>)
  then show ?case using Tm_Fv_argD by fastforce
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  then show ?case by simp
next
  case (App f a)
  from App.prems(2) have "(x, \<sigma>) \<in> fvs f \<union> fvs a" by simp
  then show ?case
  proof
    assume "(x, \<sigma>) \<in> fvs f"
    with Tm_App_argD(1)[OF App.prems(1)] App.IH(1) show ?case by blast
  next
    assume "(x, \<sigma>) \<in> fvs a"
    with Tm_App_argD(2)[OF App.prems(1)] App.IH(2) show ?case by blast
  qed
next
  case (Abs \<tau> b)
  from Abs.prems(2) have "(x, \<sigma>) \<in> fvs b" by simp
  with Tm_Abs_argD(2)[OF Abs.prems(1)] Abs.IH show ?case by blast
qed

text \<open>
  A genuine subtlety, reported here precisely rather than papered over: the side condition of
  @{text babs} (the @{text bderiv} rule for @{text Abs}-introduction) only requires the bound name @{term x} to
  avoid the free variables of @{term \<Gamma>} \emph{at that type}; @{term x} is NOT required to lie in
  @{term N}, and indeed if @{term x} occurs free in the equation being abstracted then it must
  equal some name already used in @{term "Tm_wt N \<Sigma> r"} (hence \<open>x \<in> N\<close>, recovered via
  @{thm[source] Tm_fvs_name_mem}) -- but if @{term x} occurs in neither side of the equation, the
  rule is a ``vacuous'' abstraction whose result is independent of the specific fresh @{term x}
  chosen, and EVERY name in @{term N} might already be ``used up'' as a free variable of
  @{term \<Gamma>} at that type, so enumerating @{term x} over @{term N} alone is NOT always complete.
  The fix: enumerate @{term x} over @{term "insert (fresh_name N) N"}, where @{const fresh_name}
  is one explicit name outside the finite set @{term N} (which exists because @{typ name} is
  infinite, @{thm[source] exists_fresh_name}). Since every name occurring anywhere in the bounded
  region @{term "Tm_wt N \<Sigma> r"} lies in @{term N}, @{const fresh_name} never occurs in @{term \<Gamma>},
  @{term s} or @{term t}, so it is always a valid vacuous-abstraction witness, and this two-name
  extension restores exact completeness of the enumeration (@{text rule_step_finite_correct_abs}
  below). No such fix is needed for @{text beta} or @{text inst_type},
  whose bound/instantiated names are always forced to be existing names or type variables that
  already appear in the region.
\<close>

definition step_abs :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_abs N r S = (\<Union>p1\<in>S. \<Union>\<sigma>\<in>Ty N \<Sigma> r. \<Union>x\<in>insert (fresh_name N) N.
     case dest_eq (snd p1) of
       Some (\<tau>, s, t) \<Rightarrow>
         if (\<forall>p\<in>fst p1. (x,\<sigma>)\<notin>fvs p)
            \<and> (fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N \<Sigma> r
         then {(fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))} else {}
     | None \<Rightarrow> {})"

lemma step_abs_sound: "step_abs N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_abs_def by (auto split: option.splits if_splits)

lemma finite_step_abs: "finite N \<Longrightarrow> finite (step_abs N r S)"
  using step_abs_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_abs:
  assumes finN: "finite N" and Ssub: "S \<subseteq> Sequent_r N \<Sigma> r"
  shows "step_abs N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> \<tau> s t \<sigma> x. (\<Gamma>, mk_eq \<tau> s t) \<in> S \<and> wf_ty \<Sigma> \<sigma> \<and> (\<forall>p\<in>\<Gamma>. (x,\<sigma>)\<notin>fvs p)
        \<and> q = (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
  proof
    fix q assume "q \<in> ?L"
    then obtain p1 \<sigma> xw where p1S: "p1 \<in> S" and \<sigma>mem: "\<sigma> \<in> Ty N \<Sigma> r"
      and xwmem: "xw \<in> insert (fresh_name N) N"
      and qmem: "q \<in> (case dest_eq (snd p1) of
         Some (\<tau>, s, t) \<Rightarrow>
           if (\<forall>p\<in>fst p1. (xw,\<sigma>)\<notin>fvs p)
              \<and> (fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 xw \<sigma> s)) (Abs \<sigma> (abs_fv 0 xw \<sigma> t))) \<in> Sequent_r N \<Sigma> r
           then {(fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 xw \<sigma> s)) (Abs \<sigma> (abs_fv 0 xw \<sigma> t)))} else {}
       | None \<Rightarrow> {})"
      unfolding step_abs_def by auto
    then obtain \<tau> s t where deq: "dest_eq (snd p1) = Some (\<tau>, s, t)"
      and side: "\<forall>p\<in>fst p1. (xw,\<sigma>)\<notin>fvs p"
      and qeq: "q = (fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 xw \<sigma> s)) (Abs \<sigma> (abs_fv 0 xw \<sigma> t)))"
      and tgtmem: "q \<in> Sequent_r N \<Sigma> r"
      by (auto split: option.splits if_splits)
    from dest_eq_sound[OF deq] have sndeq: "snd p1 = mk_eq \<tau> s t" .
    from p1S sndeq have p1mem: "(fst p1, mk_eq \<tau> s t) \<in> S" by (cases p1) simp
    from Ty_memD[OF \<sigma>mem] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by simp
    from tgtmem p1mem wf\<sigma> side qeq show "q \<in> ?R" by blast
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> \<tau> s t \<sigma> x where p1: "(\<Gamma>, mk_eq \<tau> s t) \<in> S" and wf\<sigma>: "wf_ty \<Sigma> \<sigma>"
      and side: "\<forall>p\<in>\<Gamma>. (x,\<sigma>)\<notin>fvs p"
      and qeq: "q = (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))"
      and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    from Ssub p1 have premmem: "(\<Gamma>, mk_eq \<tau> s t) \<in> Sequent_r N \<Sigma> r" by blast
    from premmem have cmemT: "mk_eq \<tau> s t \<in> Tm N \<Sigma> r"
      unfolding Sequent_r_def Tm_wt_def by auto
    from Tm_mk_eq_argD(1)[OF cmemT] have smemT: "s \<in> Tm N \<Sigma> r" .
    from Tm_mk_eq_argD(2)[OF cmemT] have tmemT: "t \<in> Tm N \<Sigma> r" .
    from premmem have \<Gamma>sub: "\<Gamma> \<subseteq> Tm_wt N \<Sigma> r" unfolding Sequent_r_def by auto
    from mem qeq have ccmem: "mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)) \<in> Tm_wt N \<Sigma> r"
      unfolding Sequent_r_def by auto
    from ccmem have ccmemT: "mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)) \<in> Tm N \<Sigma> r"
      unfolding Tm_wt_def by simp
    from Tm_mk_eq_argD(1)[OF ccmemT] have absmemT: "Abs \<sigma> (abs_fv 0 x \<sigma> s) \<in> Tm N \<Sigma> r" .
    from Tm_Abs_argD(1)[OF absmemT] have \<sigma>mem: "\<sigma> \<in> Ty N \<Sigma> r" .
    show "q \<in> ?L"
    proof (cases "(x,\<sigma>) \<in> fvs s \<or> (x,\<sigma>) \<in> fvs t")
      case True
      then have xmem: "x \<in> N"
        using Tm_fvs_name_mem[OF smemT] Tm_fvs_name_mem[OF tmemT] by blast
      show ?thesis
        unfolding step_abs_def
        using p1 \<sigma>mem xmem side mem qeq cmemT
        by (intro UN_I[where a = "(\<Gamma>, mk_eq \<tau> s t)"] UN_I[where a = \<sigma>] UN_I[where a = x]) simp_all
    next
      case False
      then have notin_s: "(x,\<sigma>) \<notin> fvs s" and notin_t: "(x,\<sigma>) \<notin> fvs t" by auto
      from abs_fv_id[OF notin_s] have eqs: "abs_fv 0 x \<sigma> s = s" .
      from abs_fv_id[OF notin_t] have eqt: "abs_fv 0 x \<sigma> t = t" .
      define x' where "x' = fresh_name N"
      from fresh_name_not_mem[OF finN] have xN: "x' \<notin> N" unfolding x'_def .
      have notin_s': "(x',\<sigma>) \<notin> fvs s"
        using xN Tm_fvs_name_mem[OF smemT] by blast
      have notin_t': "(x',\<sigma>) \<notin> fvs t"
        using xN Tm_fvs_name_mem[OF tmemT] by blast
      have side': "\<forall>p\<in>\<Gamma>. (x',\<sigma>) \<notin> fvs p"
      proof
        fix p assume p: "p \<in> \<Gamma>"
        with \<Gamma>sub have "p \<in> Tm N \<Sigma> r" unfolding Tm_wt_def by auto
        with xN Tm_fvs_name_mem show "(x',\<sigma>) \<notin> fvs p" by blast
      qed
      from abs_fv_id[OF notin_s'] have eqs': "abs_fv 0 x' \<sigma> s = s" .
      from abs_fv_id[OF notin_t'] have eqt': "abs_fv 0 x' \<sigma> t = t" .
      have qeq': "q = (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x' \<sigma> s)) (Abs \<sigma> (abs_fv 0 x' \<sigma> t)))"
        using qeq eqs eqt eqs' eqt' by simp
      have x'mem: "x' \<in> insert (fresh_name N) N" unfolding x'_def by simp
      show ?thesis
        unfolding step_abs_def
        using p1 \<sigma>mem x'mem side' mem qeq' cmemT
        by (intro UN_I[where a = "(\<Gamma>, mk_eq \<tau> s t)"] UN_I[where a = \<sigma>] UN_I[where a = x']) simp_all
    qed
  qed
qed

subsection \<open>\<open>inst_type\<close>: finite representative substitutions from HOL_Lite_L3\<close>

text \<open>
  For a fixed premise @{term "(\<Gamma>, c)"}, only the finitely many type variables occurring in
  @{term "\<Gamma> \<union> {c}"} (collected as @{term V} below) matter, and on @{term V} the substitution may
  be taken to range over the finite set @{term "Ty N \<Sigma> r"}
  (@{thm[source] inst_type_finite_rep}, @{text theta_restrict} from \<open>HOL_Lite_L3\<close>):
  this is exactly @{const PiE}, the finite extensional function space in \<open>FuncSet\<close>.
\<close>

definition step_inst_type :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_inst_type N r S = (\<Union>p1\<in>S.
     \<Union>f\<in>PiE (tm_tyvars (snd p1) \<union> (\<Union>p\<in>fst p1. tm_tyvars p)) (\<lambda>_. Ty N \<Sigma> r).
        let V = tm_tyvars (snd p1) \<union> (\<Union>p\<in>fst p1. tm_tyvars p);
            \<theta> = (\<lambda>a. if a \<in> V then f a else boolT)
        in if (tinst \<theta> ` fst p1, tinst \<theta> (snd p1)) \<in> Sequent_r N \<Sigma> r
           then {(tinst \<theta> ` fst p1, tinst \<theta> (snd p1))} else {})"

lemma step_inst_type_sound: "step_inst_type N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_inst_type_def by (auto simp: Let_def split: if_splits)

lemma finite_step_inst_type: "finite N \<Longrightarrow> finite (step_inst_type N r S)"
  using step_inst_type_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_inst_type:
  assumes finN: "finite N" and Ssub: "S \<subseteq> Sequent_r N \<Sigma> r"
  shows "step_inst_type N r S =
     {q \<in> Sequent_r N \<Sigma> r. \<exists>\<Gamma> c \<theta>. (\<Gamma>, c) \<in> S \<and> (\<forall>a. wf_ty \<Sigma> (\<theta> a)) \<and> q = (tinst \<theta> ` \<Gamma>, tinst \<theta> c)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
  proof
    fix q assume "q \<in> ?L"
    then obtain p1 f where p1S: "p1 \<in> S"
      and fmem: "f \<in> PiE (tm_tyvars (snd p1) \<union> (\<Union>p\<in>fst p1. tm_tyvars p)) (\<lambda>_. Ty N \<Sigma> r)"
      and qmem: "q \<in> (let V = tm_tyvars (snd p1) \<union> (\<Union>p\<in>fst p1. tm_tyvars p);
                           \<theta> = (\<lambda>a. if a \<in> V then f a else boolT)
                       in if (tinst \<theta> ` fst p1, tinst \<theta> (snd p1)) \<in> Sequent_r N \<Sigma> r
                          then {(tinst \<theta> ` fst p1, tinst \<theta> (snd p1))} else {})"
      unfolding step_inst_type_def by auto
    define V where "V = tm_tyvars (snd p1) \<union> (\<Union>p\<in>fst p1. tm_tyvars p)"
    define \<theta> where "\<theta> = (\<lambda>a. if a \<in> V then f a else boolT)"
    from qmem have qeq: "q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))"
      and tgtmem: "q \<in> Sequent_r N \<Sigma> r"
      unfolding V_def \<theta>_def Let_def by (auto split: if_splits)
    have wf\<theta>: "\<forall>a. wf_ty \<Sigma> (\<theta> a)"
    proof
      fix a show "wf_ty \<Sigma> (\<theta> a)"
      proof (cases "a \<in> V")
        case True
        with fmem have "f a \<in> Ty N \<Sigma> r" unfolding V_def by (auto simp: PiE_iff)
        with Ty_memD True show ?thesis unfolding \<theta>_def by auto
      next
        case False
        then show ?thesis unfolding \<theta>_def using wf_boolT[OF sig_ok] by simp
      qed
    qed
    from p1S wf\<theta> qeq tgtmem show "q \<in> ?R" by (cases p1) auto
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain \<Gamma> c \<theta> where p1S: "(\<Gamma>, c) \<in> S" and wf\<theta>: "\<forall>a. wf_ty \<Sigma> (\<theta> a)"
      and qeq: "q = (tinst \<theta> ` \<Gamma>, tinst \<theta> c)" and tgtmem: "q \<in> Sequent_r N \<Sigma> r" by blast
    from Ssub p1S have premmem: "(\<Gamma>, c) \<in> Sequent_r N \<Sigma> r" by blast
    from premmem have \<Gamma>sub: "\<Gamma> \<subseteq> Tm_wt N \<Sigma> r" unfolding Sequent_r_def by auto
    define V where "V = tm_tyvars c \<union> (\<Union>p\<in>\<Gamma>. tm_tyvars p)"
    define \<theta>' where "\<theta>' = theta_restrict \<theta> V"
    have wf\<theta>': "\<forall>a. wf_ty \<Sigma> (\<theta>' a)"
      unfolding \<theta>'_def using wf_ty_theta_restrict[OF wf\<theta>] by blast
    have eqc: "tinst \<theta>' c = tinst \<theta> c"
      unfolding \<theta>'_def using tinst_theta_restrict[of c V \<theta>] unfolding V_def by simp
    have eqp: "\<And>p. p \<in> \<Gamma> \<Longrightarrow> tinst \<theta>' p = tinst \<theta> p"
      unfolding \<theta>'_def using tinst_theta_restrict[of _ V \<theta>] unfolding V_def by blast
    have eq\<Gamma>: "tinst \<theta>' ` \<Gamma> = tinst \<theta> ` \<Gamma>" using eqp by force
    from qeq eqc eq\<Gamma> have qeq': "q = (tinst \<theta>' ` \<Gamma>, tinst \<theta>' c)" by simp
    from tgtmem qeq' have cmem: "tinst \<theta>' c \<in> Tm_wt N \<Sigma> r"
      and \<Gamma>'mem: "tinst \<theta>' ` \<Gamma> \<subseteq> Tm_wt N \<Sigma> r"
      unfolding Sequent_r_def by auto
    from cmem have cmemT: "tinst \<theta>' c \<in> Tm N \<Sigma> r" unfolding Tm_wt_def by simp
    have inV: "\<forall>a\<in>V. \<theta>' a \<in> Ty N \<Sigma> r"
    proof
      fix a assume aV: "a \<in> V"
      then have "a \<in> tm_tyvars c \<or> (\<exists>p\<in>\<Gamma>. a \<in> tm_tyvars p)" unfolding V_def by auto
      then show "\<theta>' a \<in> Ty N \<Sigma> r"
      proof
        assume "a \<in> tm_tyvars c"
        with cmemT inst_type_finite_rep show ?thesis by blast
      next
        assume "\<exists>p\<in>\<Gamma>. a \<in> tm_tyvars p"
        then obtain p where p: "p \<in> \<Gamma>" and ap: "a \<in> tm_tyvars p" by blast
        from p \<Gamma>'mem have "tinst \<theta>' p \<in> Tm_wt N \<Sigma> r" by blast
        then have "tinst \<theta>' p \<in> Tm N \<Sigma> r" unfolding Tm_wt_def by simp
        with ap inst_type_finite_rep show ?thesis by blast
      qed
    qed
    define f where "f = restrict \<theta>' V"
    have fPiE: "f \<in> PiE V (\<lambda>_. Ty N \<Sigma> r)"
      unfolding f_def using inV by (auto intro: PiE_I)
    have frestr: "\<And>a. a \<in> V \<Longrightarrow> f a = \<theta>' a" unfolding f_def by (simp add: restrict_apply)
    have thetaeq: "(\<lambda>a. if a \<in> V then f a else boolT) = \<theta>'"
    proof
      fix a show "(if a \<in> V then f a else boolT) = \<theta>' a"
        using frestr unfolding \<theta>'_def theta_restrict_def by (cases "a \<in> V") auto
    qed
    from p1S fPiE qeq' tgtmem show "q \<in> ?L"
      unfolding step_inst_type_def
      by (intro UN_I[where a = "(\<Gamma>,c)"] UN_I[where a = f])
         (auto simp: Let_def V_def[symmetric] thetaeq)
  qed
qed

end

subsection \<open>\<open>axiom\<close>: an explicit finite restriction oracle\<close>

text \<open>
  The axiom rule requires a finite enumeration of the axiom set @{term A} restricted to the
  bounded region @{term "Tm_wt N \<Sigma> r"}. Since @{term A} is an arbitrary (possibly infinite) set
  fixed by the @{term hol_lite} locale, this is NOT derivable from the base kernel: we extend
  the locale with an explicit oracle @{term axs} and state the restriction hypothesis openly
  as a locale assumption (the ``restricted model (a)'' of the task). Any instantiation of
  @{term hol_lite} for which @{term "A \<inter> Tm_wt N \<Sigma> r"} is computable for every finite @{term N}
  and @{term r} (e.g. any concrete finite or recursively enumerable-with-bound axiom set) gives
  rise to such an @{term axs}.
\<close>

locale hol_lite_axs = hol_lite +
  fixes axs :: "name set \<Rightarrow> nat \<Rightarrow> tm list"
  assumes axs_spec: "\<And>N r. set (axs N r) = A \<inter> Tm_wt N \<Sigma> r"

context hol_lite_axs
begin

definition step_axiom :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "step_axiom N r = (\<Union>p\<in>set (axs N r). if ({}, p) \<in> Sequent_r N \<Sigma> r then {({}, p)} else {})"

lemma step_axiom_sound: "step_axiom N r \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_axiom_def by (auto split: if_splits)

lemma finite_step_axiom: "finite N \<Longrightarrow> finite (step_axiom N r)"
  using step_axiom_sound finite_Sequent_r by (rule finite_subset)

theorem rule_step_finite_correct_axiom:
  "step_axiom N r = {q \<in> Sequent_r N \<Sigma> r. \<exists>p. p \<in> A \<and> q = ({}, p)}"
    (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
    unfolding step_axiom_def using axs_spec[of N r] by (fastforce split: if_splits)
next
  show "?R \<subseteq> ?L"
  proof
    fix q assume "q \<in> ?R"
    then obtain p where pA: "p \<in> A" and qeq: "q = ({}, p)" and mem: "q \<in> Sequent_r N \<Sigma> r" by blast
    from mem qeq have pmem: "p \<in> Tm_wt N \<Sigma> r" unfolding Sequent_r_def by auto
    from pA pmem axs_spec[of N r] have "p \<in> set (axs N r)" by blast
    with mem qeq show "q \<in> ?L"
      unfolding step_axiom_def by (intro UN_I[where a = p]) simp_all
  qed
qed

end

end
