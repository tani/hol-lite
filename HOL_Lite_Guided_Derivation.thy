theory HOL_Lite_Guided_Derivation
  imports HOL_Lite_Bounded_Derivation
begin

section \<open>Derivations relative to a hypothesis universe and a term universe\<close>

text \<open>
  @{text "bderiv N r"} accepts exactly the derivations all of whose sequents lie in the region
  @{text "Sequent_r N \<Sigma> r"} = @{text "Pow (Tm_wt N \<Sigma> r) \<times> Tm_wt N \<Sigma> r"}.  Here the region is
  @{text "Pow H \<times> U"} for two sets of terms: @{text "gderiv H U"} accepts the derivations
  all of whose hypotheses come from @{text H} and all of whose conclusions are in @{text U}.  The
  bounded search of @{text HOL_Lite_Flood} is the special case @{text "H = U = Tm_wt N \<Sigma> r"};
  a search guided by a much smaller @{text U} (subterms of the goal and axioms, say) and an
  @{text H} of just the hypotheses of the goal decides @{text gderiv} for those sets:

    \<^item> soundness holds for every @{text H} and @{text U} (@{text gderiv_sound});
    \<^item> completeness holds relative to them: every derivation that stays inside the region is
      found (this is the characterisation of the guided search proved later);
    \<^item> completeness holds in the limit: a goal is derivable iff it is @{text gderiv} for some
      finite @{text H} and @{text U} (@{text derivable_iff_gderiv}), and enlarging them never
      loses a derivation (@{text gderiv_mono}).
\<close>

context hol_lite
begin

definition Sequent_HU :: "tm set \<Rightarrow> tm set \<Rightarrow> (tm set \<times> tm) set" where
  "Sequent_HU H U = Pow H \<times> U"

lemma Sequent_r_eq_HU: "Sequent_r N \<Sigma> r = Sequent_HU (Tm_wt N \<Sigma> r) (Tm_wt N \<Sigma> r)"
  by (simp add: Sequent_r_def Sequent_HU_def)

lemma Sequent_HU_mono: "H \<subseteq> H' \<Longrightarrow> U \<subseteq> U' \<Longrightarrow> Sequent_HU H U \<subseteq> Sequent_HU H' U'"
  unfolding Sequent_HU_def by auto

inductive gderiv :: "tm set \<Rightarrow> tm set \<Rightarrow> tm set \<times> tm \<Rightarrow> bool" for H U where
  grefl: "has_type \<Sigma> [] t \<tau> \<Longrightarrow> ({}, mk_eq \<tau> t t) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U ({}, mk_eq \<tau> t t)"
| gtrans: "gderiv H U (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> gderiv H U (\<Delta>, mk_eq \<tau> t u)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)"
| gmk_comb: "gderiv H U (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) \<Longrightarrow> gderiv H U (\<Delta>, mk_eq \<sigma> a b)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))"
| gabs: "gderiv H U (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<Longrightarrow> (\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p)
            \<Longrightarrow> (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))"
| gbeta: "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)
            \<Longrightarrow> ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))"
| gassm: "has_type \<Sigma> [] p boolT \<Longrightarrow> ({p}, p) \<in> Sequent_HU H U \<Longrightarrow> gderiv H U ({p}, p)"
| geq_mp: "gderiv H U (\<Gamma>, mk_eq boolT p q) \<Longrightarrow> gderiv H U (\<Delta>, p)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, q) \<in> Sequent_HU H U \<Longrightarrow> gderiv H U (\<Gamma> \<union> \<Delta>, q)"
| gdeduct_antisym: "gderiv H U (\<Gamma>, p) \<Longrightarrow> gderiv H U (\<Delta>, q)
            \<Longrightarrow> ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q)"
| ginst_type: "gderiv H U (\<Gamma>, c) \<Longrightarrow> (\<And>a. wf_ty \<Sigma> (\<theta> a))
            \<Longrightarrow> (tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_HU H U
            \<Longrightarrow> gderiv H U (tinst \<theta> ` \<Gamma>, tinst \<theta> c)"
| gaxiom: "p \<in> A \<Longrightarrow> ({}, p) \<in> Sequent_HU H U \<Longrightarrow> gderiv H U ({}, p)"

subsection \<open>Soundness\<close>

lemma gderiv_sound_aux: "gderiv H U p \<Longrightarrow> derivable (fst p) (snd p)"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  then show ?case by (auto intro: derivable.refl)
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: derivable.trans)
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: derivable.mk_comb)
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: derivable.abs)
next
  case (gbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: derivable.beta)
next
  case (gassm p)
  then show ?case by (auto intro: derivable.assm)
next
  case (geq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: derivable.eq_mp)
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: derivable.deduct_antisym)
next
  case (ginst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: derivable.inst_type)
next
  case (gaxiom p)
  then show ?case by (auto intro: derivable.axiom)
qed

lemma gderiv_sound: "gderiv H U (\<Gamma>, c) \<Longrightarrow> derivable \<Gamma> c"
  using gderiv_sound_aux[of H U "(\<Gamma>, c)"] by simp

subsection \<open>Monotonicity in the universe\<close>

lemma gderiv_mono: "gderiv H U p \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> U \<subseteq> U' \<Longrightarrow> gderiv H' U' p"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  then show ?case using Sequent_HU_mono[OF grefl.prems(1) grefl.prems(2)] by (auto intro: gderiv.intros)
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case using Sequent_HU_mono[OF gtrans.prems(1) gtrans.prems(2)] by (auto intro: gderiv.intros)
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case using Sequent_HU_mono[OF gmk_comb.prems(1) gmk_comb.prems(2)] by (auto intro: gderiv.intros)
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case using Sequent_HU_mono[OF gabs.prems(1) gabs.prems(2)] by (auto intro: gderiv.intros)
next
  case (gbeta \<sigma> b \<tau> x)
  then show ?case using Sequent_HU_mono[OF gbeta.prems(1) gbeta.prems(2)] by (auto intro: gderiv.intros)
next
  case (gassm p)
  then show ?case using Sequent_HU_mono[OF gassm.prems(1) gassm.prems(2)] by (auto intro: gderiv.intros)
next
  case (geq_mp \<Gamma> p q \<Delta>)
  then show ?case using Sequent_HU_mono[OF geq_mp.prems(1) geq_mp.prems(2)] by (auto intro: gderiv.intros)
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case using Sequent_HU_mono[OF gdeduct_antisym.prems(1) gdeduct_antisym.prems(2)] by (auto intro: gderiv.intros)
next
  case (ginst_type \<Gamma> c \<theta>)
  then show ?case using Sequent_HU_mono[OF ginst_type.prems(1) ginst_type.prems(2)] by (auto intro: gderiv.intros)
next
  case (gaxiom p)
  then show ?case using Sequent_HU_mono[OF gaxiom.prems(1) gaxiom.prems(2)] by (auto intro: gderiv.intros)
qed

subsection \<open>The bounded derivations are the case @{text "U = Tm_wt N \<Sigma> r"}\<close>

lemma bderiv_imp_gderiv: "bderiv N r p \<Longrightarrow> gderiv (Tm_wt N \<Sigma> r) (Tm_wt N \<Sigma> r) p"
proof (induction rule: bderiv.induct)
  case (brefl t \<tau>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (bbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (bassm p)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (beq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (binst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
next
  case (baxiom p)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_HU)
qed

lemma gderiv_imp_bderiv: "gderiv (Tm_wt N \<Sigma> r) (Tm_wt N \<Sigma> r) p \<Longrightarrow> bderiv N r p"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gassm p)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (geq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (ginst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
next
  case (gaxiom p)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_HU)
qed

theorem bderiv_iff_gderiv: "bderiv N r p \<longleftrightarrow> gderiv (Tm_wt N \<Sigma> r) (Tm_wt N \<Sigma> r) p"
  using bderiv_imp_gderiv gderiv_imp_bderiv by blast

subsection \<open>Completeness in the limit\<close>

theorem derivable_iff_gderiv:
  "derivable \<Gamma> c \<longleftrightarrow> (\<exists>H U. finite H \<and> finite U \<and> gderiv H U (\<Gamma>, c))"
proof
  assume "derivable \<Gamma> c"
  then obtain N r where fn: "finite N" and b: "bderiv N r (\<Gamma>, c)"
    using derivable_iff_bderiv by blast
  from b have "gderiv (Tm_wt N \<Sigma> r) (Tm_wt N \<Sigma> r) (\<Gamma>, c)" by (simp add: bderiv_iff_gderiv)
  moreover have "finite (Tm_wt N \<Sigma> r)" using fn by (rule finite_Tm_wt)
  ultimately show "\<exists>H U. finite H \<and> finite U \<and> gderiv H U (\<Gamma>, c)" by blast
next
  assume "\<exists>H U. finite H \<and> finite U \<and> gderiv H U (\<Gamma>, c)"
  then show "derivable \<Gamma> c" using gderiv_sound by blast
qed

end

end
