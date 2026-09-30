theory HOL_Lite_Guided_Derivation
  imports HOL_Lite_Bounded_Derivation
begin

section \<open>Derivations relative to a term universe\<close>

text \<open>
  @{text "bderiv N r"} accepts exactly the derivations all of whose sequents lie in the region
  @{text "Sequent_r N \<Sigma> r"} = @{text "Pow (Tm_wt N \<Sigma> r) \<times> Tm_wt N \<Sigma> r"}.  Here the region is any set
  @{text U} of terms: @{text "gderiv U"} accepts the derivations all of whose hypotheses and
  conclusions are built from @{text U}.  The bounded search of @{text HOL_Lite_Flood} is then the
  special case @{text "U = Tm_wt N \<Sigma> r"}, while a search guided by a much smaller @{text U}
  (subterms of the goal and axioms, say) decides @{text gderiv} for that @{text U}:

    \<^item> soundness holds for every @{text U} (@{text gderiv_sound});
    \<^item> completeness holds relative to @{text U}: every derivation that stays inside @{text U}
      is found (this is the characterisation of the guided search proved later);
    \<^item> completeness holds in the limit: a goal is derivable iff it is @{text gderiv} for some
      finite @{text U} (@{text derivable_iff_gderiv}), and enlarging @{text U} never loses a
      derivation (@{text gderiv_mono}).
\<close>

context hol_lite
begin

definition Sequent_U :: "tm set \<Rightarrow> (tm set \<times> tm) set" where
  "Sequent_U U = Pow U \<times> U"

lemma Sequent_r_eq_U: "Sequent_r N \<Sigma> r = Sequent_U (Tm_wt N \<Sigma> r)"
  by (simp add: Sequent_r_def Sequent_U_def)

lemma Sequent_U_mono: "U \<subseteq> V \<Longrightarrow> Sequent_U U \<subseteq> Sequent_U V"
  unfolding Sequent_U_def by auto

inductive gderiv :: "tm set \<Rightarrow> tm set \<times> tm \<Rightarrow> bool" for U where
  grefl: "has_type \<Sigma> [] t \<tau> \<Longrightarrow> ({}, mk_eq \<tau> t t) \<in> Sequent_U U
            \<Longrightarrow> gderiv U ({}, mk_eq \<tau> t t)"
| gtrans: "gderiv U (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> gderiv U (\<Delta>, mk_eq \<tau> t u)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_U U
            \<Longrightarrow> gderiv U (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)"
| gmk_comb: "gderiv U (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) \<Longrightarrow> gderiv U (\<Delta>, mk_eq \<sigma> a b)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_U U
            \<Longrightarrow> gderiv U (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))"
| gabs: "gderiv U (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<Longrightarrow> (\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p)
            \<Longrightarrow> (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_U U
            \<Longrightarrow> gderiv U (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))"
| gbeta: "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)
            \<Longrightarrow> ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_U U
            \<Longrightarrow> gderiv U ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))"
| gassm: "has_type \<Sigma> [] p boolT \<Longrightarrow> ({p}, p) \<in> Sequent_U U \<Longrightarrow> gderiv U ({p}, p)"
| geq_mp: "gderiv U (\<Gamma>, mk_eq boolT p q) \<Longrightarrow> gderiv U (\<Delta>, p)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, q) \<in> Sequent_U U \<Longrightarrow> gderiv U (\<Gamma> \<union> \<Delta>, q)"
| gdeduct_antisym: "gderiv U (\<Gamma>, p) \<Longrightarrow> gderiv U (\<Delta>, q)
            \<Longrightarrow> ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_U U
            \<Longrightarrow> gderiv U ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q)"
| ginst_type: "gderiv U (\<Gamma>, c) \<Longrightarrow> (\<And>a. wf_ty \<Sigma> (\<theta> a))
            \<Longrightarrow> (tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_U U
            \<Longrightarrow> gderiv U (tinst \<theta> ` \<Gamma>, tinst \<theta> c)"
| gaxiom: "p \<in> A \<Longrightarrow> ({}, p) \<in> Sequent_U U \<Longrightarrow> gderiv U ({}, p)"

subsection \<open>Soundness\<close>

lemma gderiv_sound_aux: "gderiv U p \<Longrightarrow> derivable (fst p) (snd p)"
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

lemma gderiv_sound: "gderiv U (\<Gamma>, c) \<Longrightarrow> derivable \<Gamma> c"
  using gderiv_sound_aux[of U "(\<Gamma>, c)"] by simp

subsection \<open>Monotonicity in the universe\<close>

lemma gderiv_mono: "gderiv U p \<Longrightarrow> U \<subseteq> V \<Longrightarrow> gderiv V p"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  then show ?case using Sequent_U_mono[OF grefl.prems] by (auto intro: gderiv.intros)
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case using Sequent_U_mono[OF gtrans.prems] by (auto intro: gderiv.intros)
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case using Sequent_U_mono[OF gmk_comb.prems] by (auto intro: gderiv.intros)
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case using Sequent_U_mono[OF gabs.prems] by (auto intro: gderiv.intros)
next
  case (gbeta \<sigma> b \<tau> x)
  then show ?case using Sequent_U_mono[OF gbeta.prems] by (auto intro: gderiv.intros)
next
  case (gassm p)
  then show ?case using Sequent_U_mono[OF gassm.prems] by (auto intro: gderiv.intros)
next
  case (geq_mp \<Gamma> p q \<Delta>)
  then show ?case using Sequent_U_mono[OF geq_mp.prems] by (auto intro: gderiv.intros)
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case using Sequent_U_mono[OF gdeduct_antisym.prems] by (auto intro: gderiv.intros)
next
  case (ginst_type \<Gamma> c \<theta>)
  then show ?case using Sequent_U_mono[OF ginst_type.prems] by (auto intro: gderiv.intros)
next
  case (gaxiom p)
  then show ?case using Sequent_U_mono[OF gaxiom.prems] by (auto intro: gderiv.intros)
qed

subsection \<open>The bounded derivations are the case @{text "U = Tm_wt N \<Sigma> r"}\<close>

lemma bderiv_imp_gderiv: "bderiv N r p \<Longrightarrow> gderiv (Tm_wt N \<Sigma> r) p"
proof (induction rule: bderiv.induct)
  case (brefl t \<tau>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (bbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (bassm p)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (beq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (binst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
next
  case (baxiom p)
  then show ?case by (auto intro: gderiv.intros simp: Sequent_r_eq_U)
qed

lemma gderiv_imp_bderiv: "gderiv (Tm_wt N \<Sigma> r) p \<Longrightarrow> bderiv N r p"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gassm p)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (geq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (ginst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
next
  case (gaxiom p)
  then show ?case by (auto intro: bderiv.intros simp: Sequent_r_eq_U)
qed

theorem bderiv_iff_gderiv: "bderiv N r p \<longleftrightarrow> gderiv (Tm_wt N \<Sigma> r) p"
  using bderiv_imp_gderiv gderiv_imp_bderiv by blast

subsection \<open>Completeness in the limit\<close>

theorem derivable_iff_gderiv: "derivable \<Gamma> c \<longleftrightarrow> (\<exists>U. finite U \<and> gderiv U (\<Gamma>, c))"
proof
  assume "derivable \<Gamma> c"
  then obtain N r where fn: "finite N" and b: "bderiv N r (\<Gamma>, c)"
    using derivable_iff_bderiv by blast
  from b have "gderiv (Tm_wt N \<Sigma> r) (\<Gamma>, c)" by (simp add: bderiv_iff_gderiv)
  moreover have "finite (Tm_wt N \<Sigma> r)" using fn by (rule finite_Tm_wt)
  ultimately show "\<exists>U. finite U \<and> gderiv U (\<Gamma>, c)" by blast
next
  assume "\<exists>U. finite U \<and> gderiv U (\<Gamma>, c)"
  then show "derivable \<Gamma> c" using gderiv_sound by blast
qed

end

end
