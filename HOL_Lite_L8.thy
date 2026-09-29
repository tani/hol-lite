theory HOL_Lite_L8
  imports HOL_Lite_L7
begin

section \<open>Abstract finite-region saturation\<close>

text \<open>The following operators are finite set expressions, not executable list enumerators.
  In particular, finiteness alone does not establish code generation or running time.\<close>

lemma finite_inflationary_stabilises:
  fixes F :: "'a set \<Rightarrow> 'a set"
  assumes fin: "finite U"
    and bounded: "\<And>S. S \<subseteq> U \<Longrightarrow> F S \<subseteq> U"
    and inflation: "\<And>S. S \<subseteq> U \<Longrightarrow> S \<subseteq> F S"
  shows "\<exists>k \<le> card U. (F ^^ k) {} = F ((F ^^ k) {})"
proof -
  have aux: "\<And>m S. S \<subseteq> U \<Longrightarrow> card (U - S) \<le> m \<Longrightarrow>
      \<exists>k \<le> m. (F ^^ k) S = F ((F ^^ k) S)"
  proof -
    fix m
    show "\<And>S. S \<subseteq> U \<Longrightarrow> card (U - S) \<le> m \<Longrightarrow> \<exists>k \<le> m. (F ^^ k) S = F ((F ^^ k) S)"
    proof (induction m)
    case 0
    then have eq: "S = U" using fin by (auto simp: card_eq_0_iff)
    have "F S = S"
      using bounded[OF \<open>S \<subseteq> U\<close>] inflation[OF \<open>S \<subseteq> U\<close>] eq by auto
    then show ?case by (intro exI[of _ 0]) simp
  next
    case (Suc m)
    show ?case
    proof (cases "F S = S")
      case True
      then show ?thesis by (intro exI[of _ 0]) simp
    next
      case False
      from Suc.prems have sub: "S \<subseteq> U" by simp
      have fsub: "F S \<subseteq> U" using bounded[OF sub] .
      have less: "card (U - F S) < card (U - S)"
        using fin sub fsub False inflation[OF sub]
        by (intro psubset_card_mono) auto
      with Suc.prems have le: "card (U - F S) \<le> m" by simp
      from Suc.IH[OF fsub le] obtain k where k: "k \<le> m"
        and stable: "(F ^^ k) (F S) = F ((F ^^ k) (F S))" by blast
      have commute: "(F ^^ k) (F S) = F ((F ^^ k) S)"
        by (induction k) simp_all
      have "(F ^^ Suc k) S = F ((F ^^ Suc k) S)"
        using stable commute by (simp add: funpow_Suc_right)
      with k show ?thesis by (intro exI[of _ "Suc k"]) auto
    qed
    qed
  qed
  from aux[of "{}" "card U"] show ?thesis by simp
qed

lemma finite_inflationary_card_fixed:
  fixes F :: "'a set \<Rightarrow> 'a set"
  assumes fin: "finite U"
    and bounded: "\<And>S. S \<subseteq> U \<Longrightarrow> F S \<subseteq> U"
    and inflation: "\<And>S. S \<subseteq> U \<Longrightarrow> S \<subseteq> F S"
  shows "(F ^^ card U) {} = F ((F ^^ card U) {})"
proof -
  from finite_inflationary_stabilises[OF assms]
  obtain k where k: "k \<le> card U" and fixed: "(F ^^ k) {} = F ((F ^^ k) {})" by blast
  have later: "\<And>j. (F ^^ (k + j)) {} = (F ^^ k) {}"
  proof -
    fix j show "(F ^^ (k + j)) {} = (F ^^ k) {}"
    proof (induction j)
      case 0
      then show ?case by simp
    next
      case (Suc j)
      then show ?case using fixed by (simp add: funpow_Suc_right)
    qed
  qed
  from later[of "card U - k"] k fixed show ?thesis by simp
qed

context hol_lite_axs
begin

definition step_r :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "step_r N r S = step_refl N r \<union> step_assm N r \<union> step_beta N r \<union> step_axiom N r
      \<union> step_trans N r S \<union> step_mk_comb N r S \<union> step_abs N r S
      \<union> step_eq_mp N r S \<union> step_deduct_antisym N r S \<union> step_inst_type N r S"

definition grow_r :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set \<Rightarrow> (tm set \<times> tm) set" where
  "grow_r N r S = S \<union> step_r N r S"

lemma step_r_subset: "step_r N r S \<subseteq> Sequent_r N \<Sigma> r"
  unfolding step_r_def
  using step_refl_sound[of N r] step_assm_sound[of N r] step_beta_sound[of N r]
    step_axiom_sound[of N r] step_trans_sound[of N r S] step_mk_comb_sound[of N r S]
    step_abs_sound[of N r S] step_eq_mp_sound[of N r S]
    step_deduct_antisym_sound[of N r S] step_inst_type_sound[of N r S] by auto

lemma step_trans_mono: "S \<subseteq> T \<Longrightarrow> step_trans N r S \<subseteq> step_trans N r T"
  unfolding step_trans_def by (intro UN_mono) auto

lemma step_mk_comb_mono: "S \<subseteq> T \<Longrightarrow> step_mk_comb N r S \<subseteq> step_mk_comb N r T"
  unfolding step_mk_comb_def by (intro UN_mono) auto

lemma step_abs_mono: "S \<subseteq> T \<Longrightarrow> step_abs N r S \<subseteq> step_abs N r T"
  unfolding step_abs_def by (intro UN_mono) auto

lemma step_eq_mp_mono: "S \<subseteq> T \<Longrightarrow> step_eq_mp N r S \<subseteq> step_eq_mp N r T"
  unfolding step_eq_mp_def by (intro UN_mono) auto

lemma step_deduct_antisym_mono: "S \<subseteq> T \<Longrightarrow> step_deduct_antisym N r S \<subseteq> step_deduct_antisym N r T"
  unfolding step_deduct_antisym_def by (intro UN_mono) auto

lemma step_inst_type_mono: "S \<subseteq> T \<Longrightarrow> step_inst_type N r S \<subseteq> step_inst_type N r T"
  unfolding step_inst_type_def by (intro UN_mono) auto

lemma step_r_mono: "S \<subseteq> T \<Longrightarrow> step_r N r S \<subseteq> step_r N r T"
  using step_trans_mono[of S T N r] step_mk_comb_mono[of S T N r]
    step_abs_mono[of S T N r] step_eq_mp_mono[of S T N r]
    step_deduct_antisym_mono[of S T N r] step_inst_type_mono[of S T N r]
  unfolding step_r_def by auto

lemma grow_r_mono: "S \<subseteq> T \<Longrightarrow> grow_r N r S \<subseteq> grow_r N r T"
  using step_r_mono unfolding grow_r_def by blast

lemma grow_r_subset: "S \<subseteq> Sequent_r N \<Sigma> r \<Longrightarrow> grow_r N r S \<subseteq> Sequent_r N \<Sigma> r"
  using step_r_subset unfolding grow_r_def by blast

definition sat_r :: "name set \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "sat_r N r = lfp (grow_r N r)"

lemma grow_r_mono_fun: "mono (grow_r N r)"
  using grow_r_mono unfolding mono_def by blast

lemma sat_r_closed: "grow_r N r (sat_r N r) = sat_r N r"
  unfolding sat_r_def by (rule sym, rule lfp_unfold[OF grow_r_mono_fun])

lemma sat_r_subset: "sat_r N r \<subseteq> Sequent_r N \<Sigma> r"
  unfolding sat_r_def
  by (rule lfp_lowerbound) (simp add: grow_r_subset)

lemma step_r_sat_subset: "step_r N r (sat_r N r) \<subseteq> sat_r N r"
  using sat_r_closed unfolding grow_r_def by blast

lemma bderiv_region: "bderiv N r p \<Longrightarrow> p \<in> Sequent_r N \<Sigma> r"
  by (induction rule: bderiv.induct) auto

lemma sat_r_sound:
  assumes finN: "finite N"
  shows "sat_r N r \<subseteq> {p. bderiv N r p}"
proof (unfold sat_r_def, rule lfp_lowerbound)
  let ?B = "{p. bderiv N r p}"
  have Bsub: "?B \<subseteq> Sequent_r N \<Sigma> r" using bderiv_region by blast
  show "grow_r N r ?B \<subseteq> ?B"
    unfolding grow_r_def step_r_def
    using finN Bsub
    by (auto simp: rule_step_finite_correct_refl rule_step_finite_correct_assm
      rule_step_finite_correct_beta rule_step_finite_correct_axiom
      rule_step_finite_correct_trans rule_step_finite_correct_mk_comb
      rule_step_finite_correct_abs[OF finN Bsub]
      rule_step_finite_correct_eq_mp rule_step_finite_correct_deduct_antisym
      rule_step_finite_correct_inst_type[OF finN Bsub]
      intro: bderiv.intros)
qed

lemma bderiv_sat_r:
  assumes finN: "finite N" and der: "bderiv N r p"
  shows "p \<in> sat_r N r"
  using der
proof (induction rule: bderiv.induct)
  case (brefl t \<tau>)
  then show ?case using sat_r_subset[of N r] step_r_sat_subset[of N r]
    by (auto simp: step_r_def rule_step_finite_correct_refl)
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  have in_step: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> step_trans N r (sat_r N r)"
    using btrans.hyps btrans.IH
    by (simp add: rule_step_finite_correct_trans; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  have in_step: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> step_mk_comb N r (sat_r N r)"
    using bmk_comb.hyps bmk_comb.IH
    by (simp add: rule_step_finite_correct_mk_comb; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  have in_step: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
    \<in> step_abs N r (sat_r N r)"
    using babs.hyps babs.IH
    by (simp add: rule_step_finite_correct_abs[OF finN sat_r_subset]; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (bbeta \<sigma> b \<tau> x)
  have in_step: "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> step_beta N r"
    using bbeta.hyps by (simp add: rule_step_finite_correct_beta; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (bassm p)
  have in_step: "({p}, p) \<in> step_assm N r"
    using bassm.hyps by (simp add: rule_step_finite_correct_assm; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (beq_mp \<Gamma> p q \<Delta>)
  have in_step: "(\<Gamma> \<union> \<Delta>, q) \<in> step_eq_mp N r (sat_r N r)"
    using beq_mp.hyps beq_mp.IH by (simp add: rule_step_finite_correct_eq_mp; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  have in_step: "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q)
    \<in> step_deduct_antisym N r (sat_r N r)"
    using bdeduct_antisym.hyps bdeduct_antisym.IH
    by (simp add: rule_step_finite_correct_deduct_antisym; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (binst_type \<Gamma> c \<theta>)
  have in_step: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> step_inst_type N r (sat_r N r)"
    using binst_type.hyps binst_type.IH
    by (simp add: rule_step_finite_correct_inst_type[OF finN sat_r_subset]; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
next
  case (baxiom p)
  have in_step: "({}, p) \<in> step_axiom N r"
    using baxiom.hyps by (simp add: rule_step_finite_correct_axiom; blast)
  from in_step step_r_sat_subset[of N r] show ?case
    unfolding step_r_def by blast
qed

definition iterate_r :: "name set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "iterate_r N r k = (grow_r N r ^^ k) {}"

lemma iterate_r_subset: "iterate_r N r k \<subseteq> Sequent_r N \<Sigma> r"
  unfolding iterate_r_def
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case using grow_r_subset[of "iterate_r N r k" N r]
    by (simp add: iterate_r_def funpow_Suc_right)
qed

lemma iterate_r_sat_subset: "iterate_r N r k \<subseteq> sat_r N r"
  unfolding iterate_r_def
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  with grow_r_mono[of "(grow_r N r ^^ k) {}" "sat_r N r" N r]
  show ?case using sat_r_closed[of N r] by (simp add: funpow_Suc_right)
qed

theorem sat_r_finite_iteration:
  assumes finN: "finite N"
  shows "sat_r N r = iterate_r N r (card (Sequent_r N \<Sigma> r))"
proof -
  let ?U = "Sequent_r N \<Sigma> r"
  have finU: "finite ?U" using finite_Sequent_r[OF finN] .
  have preserve: "\<And>S. S \<subseteq> ?U \<Longrightarrow> grow_r N r S \<subseteq> ?U"
    using grow_r_subset by blast
  have infl: "\<And>S. S \<subseteq> ?U \<Longrightarrow> S \<subseteq> grow_r N r S"
    unfolding grow_r_def by auto
  have fixed: "grow_r N r (iterate_r N r (card ?U)) = iterate_r N r (card ?U)"
    using finite_inflationary_card_fixed[OF finU preserve infl]
    unfolding iterate_r_def by simp
  have lower: "sat_r N r \<subseteq> iterate_r N r (card ?U)"
  proof -
    have "grow_r N r (iterate_r N r (card ?U)) \<subseteq> iterate_r N r (card ?U)"
      using fixed by simp
    then show ?thesis unfolding sat_r_def by (rule lfp_lowerbound)
  qed
  from lower iterate_r_sat_subset[of N r "card ?U"] show ?thesis by blast
qed

theorem sat_r_iff_bderiv:
  assumes "finite N"
  shows "p \<in> sat_r N r \<longleftrightarrow> bderiv N r p"
  using sat_r_sound[OF assms] bderiv_sat_r[OF assms] by blast


text \<open>For a fixed finite name set and size radius, iterating exactly the cardinality of
  the sequent region characterizes clipped derivations; no larger fixed-point iteration
  is needed. The final existential equivalence ranges over all such regions and is not
  a decision procedure for unrestricted derivability. In particular, the set operators,
  finite representatives, and axiom oracle require executable implementations.
  HOL_Lite_Executable_Waterfall supplies these for a finite name list and an axiom
  enumerator satisfying hol_lite_axs; this theorem alone does not run the search.\<close>

theorem bounded_iteration_iff_bderiv:
  assumes "finite N"
  shows "p \<in> iterate_r N r (card (Sequent_r N \<Sigma> r)) \<longleftrightarrow> bderiv N r p"
  using sat_r_finite_iteration[OF assms] sat_r_iff_bderiv[OF assms] by simp

corollary bounded_iteration_sound:
  assumes "finite N" and "(\<Gamma>, c) \<in> iterate_r N r (card (Sequent_r N \<Sigma> r))"
  shows "derivable \<Gamma> c"
  using bounded_iteration_iff_bderiv[OF assms(1)] assms(2) bderiv_sound by blast

theorem derivable_iff_finite_iteration:
  "derivable \<Gamma> c \<longleftrightarrow> (\<exists>N r. finite N \<and>
     (\<Gamma>, c) \<in> iterate_r N r (card (Sequent_r N \<Sigma> r)))"
proof -
  have eq: "\<And>N r. finite N \<Longrightarrow>
    ((\<Gamma>, c) \<in> iterate_r N r (card (Sequent_r N \<Sigma> r))) = bderiv N r (\<Gamma>, c)"
    using bounded_iteration_iff_bderiv by blast
  show ?thesis using derivable_iff_bderiv eq by (metis (mono_tags, lifting))
qed

end
end
