theory HOL_Lite_Bounded_Derivation
  imports HOL_Lite_Search_Spaces HOL_Lite_Checker_Completeness HOL_Lite_Kernel
begin

section \<open>A clipped step relation on the bounded search space\<close>

context hol_lite
begin

text \<open>
  The region @{term "Sequent_r N \<Sigma> r"} from \<open>HOL_Lite_Search_Spaces\<close> is NOT closed under the rules of
  @{const derivable}: \<open>abs\<close>, \<open>beta\<close> and \<open>inst_type\<close> may produce names or sizes outside @{term N},
  @{term r}.  We therefore define a CLIPPED step @{term "bderiv N r"}: the same rules as
  @{const derivable} (minus \<open>inst\<close>, whose premise is unsatisfiable, see below), where every
  premise sequent and the conclusion sequent are additionally required to lie in
  @{term "Sequent_r N \<Sigma> r"}.  No closure theorem is claimed; instead we prove soundness,
  monotonicity in @{term N} and @{term r}, and that the union over all finite @{term N} and all
  @{term r} recovers exactly @{const derivable}.
\<close>

subsection \<open>Helper facts about names, typing and the region\<close>

lemma finite_ty_names [simp]: "finite (ty_names \<tau>)"
  by (induction \<tau> rule: ty_names.induct) auto

lemma finite_tm_names [simp]: "finite (tm_names t)"
  by (induction t rule: tm_names.induct) auto

text \<open>Every type annotation occurring in a well-typed term is well-formed.\<close>

lemma has_type_wf_tm_ty: "has_type \<Sigma> \<Gamma> t \<tau> \<Longrightarrow> wf_tm_ty \<Sigma> t"
  by (induction rule: has_type.induct) auto

lemma Sequent_r_mono_r: "r \<le> r' \<Longrightarrow> Sequent_r N \<Sigma> r \<subseteq> Sequent_r N \<Sigma> r'"
  using Tm_wt_mono_r[of r r' N \<Sigma>] unfolding Sequent_r_def by auto

lemma Sequent_r_mono_N: "N \<subseteq> N' \<Longrightarrow> Sequent_r N \<Sigma> r \<subseteq> Sequent_r N' \<Sigma> r"
  using Tm_wt_mono_N[of N N' \<Sigma> r] unfolding Sequent_r_def by auto

subsection \<open>The clipped step relation\<close>

inductive bderiv :: "name set \<Rightarrow> nat \<Rightarrow> tm set \<times> tm \<Rightarrow> bool" for N r where
  brefl: "has_type \<Sigma> [] t \<tau> \<Longrightarrow> ({}, mk_eq \<tau> t t) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r ({}, mk_eq \<tau> t t)"
| btrans: "bderiv N r (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> bderiv N r (\<Delta>, mk_eq \<tau> t u)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)"
| bmk_comb: "bderiv N r (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) \<Longrightarrow> bderiv N r (\<Delta>, mk_eq \<sigma> a b)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))"
| babs: "bderiv N r (\<Gamma>, mk_eq \<tau> s t) \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<Longrightarrow> (\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p)
            \<Longrightarrow> (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r (\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))"
| bbeta: "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)
            \<Longrightarrow> ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r ({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))"
| bassm: "has_type \<Sigma> [] p boolT \<Longrightarrow> ({p}, p) \<in> Sequent_r N \<Sigma> r \<Longrightarrow> bderiv N r ({p}, p)"
| beq_mp: "bderiv N r (\<Gamma>, mk_eq boolT p q) \<Longrightarrow> bderiv N r (\<Delta>, p)
            \<Longrightarrow> (\<Gamma> \<union> \<Delta>, q) \<in> Sequent_r N \<Sigma> r \<Longrightarrow> bderiv N r (\<Gamma> \<union> \<Delta>, q)"
| bdeduct_antisym: "bderiv N r (\<Gamma>, p) \<Longrightarrow> bderiv N r (\<Delta>, q)
            \<Longrightarrow> ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q)"
| binst_type: "bderiv N r (\<Gamma>, c) \<Longrightarrow> (\<And>a. wf_ty \<Sigma> (\<theta> a))
            \<Longrightarrow> (tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_r N \<Sigma> r
            \<Longrightarrow> bderiv N r (tinst \<theta> ` \<Gamma>, tinst \<theta> c)"
| baxiom: "p \<in> A \<Longrightarrow> ({}, p) \<in> Sequent_r N \<Sigma> r \<Longrightarrow> bderiv N r ({}, p)"

subsection \<open>Soundness\<close>

text \<open>
  Proved on an atomic pair variable @{term p} first (so that rule induction generalizes cleanly),
  then specialised to the @{term "(\<Gamma>, c)"} notation used throughout.
\<close>

lemma bderiv_sound_aux: "bderiv N r p \<Longrightarrow> derivable (fst p) (snd p)"
proof (induction rule: bderiv.induct)
  case (brefl t \<tau>)
  then show ?case by (auto intro: derivable.refl)
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  then show ?case by (auto intro: derivable.trans)
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  then show ?case by (auto intro: derivable.mk_comb)
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  then show ?case by (auto intro: derivable.abs)
next
  case (bbeta \<sigma> b \<tau> x)
  then show ?case by (auto intro: derivable.beta)
next
  case (bassm p)
  then show ?case by (auto intro: derivable.assm)
next
  case (beq_mp \<Gamma> p q \<Delta>)
  then show ?case by (auto intro: derivable.eq_mp)
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  then show ?case by (auto intro: derivable.deduct_antisym)
next
  case (binst_type \<Gamma> c \<theta>)
  then show ?case by (auto intro: derivable.inst_type)
next
  case (baxiom p)
  then show ?case by (auto intro: derivable.axiom)
qed

lemma bderiv_sound: "bderiv N r (\<Gamma>, c) \<Longrightarrow> derivable \<Gamma> c"
  using bderiv_sound_aux[of N r "(\<Gamma>, c)"] by simp

subsection \<open>Monotonicity in \<^term>\<open>r\<close> and \<^term>\<open>N\<close>\<close>

lemma bderiv_mono_r_aux: "bderiv N r p \<Longrightarrow> r \<le> r' \<Longrightarrow> bderiv N r' p"
proof (induction arbitrary: r' rule: bderiv.induct)
  case (brefl t \<tau>)
  from Sequent_r_mono_r[OF brefl.prems] brefl.hyps(2)
  have mem: "({}, mk_eq \<tau> t t) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.brefl[OF brefl.hyps(1) mem] show ?case .
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  from btrans.IH(1)[OF btrans.prems] have b1: "bderiv N r' (\<Gamma>, mk_eq \<tau> s t)" .
  from btrans.IH(2)[OF btrans.prems] have b2: "bderiv N r' (\<Delta>, mk_eq \<tau> t u)" .
  from Sequent_r_mono_r[OF btrans.prems] btrans.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.btrans[OF b1 b2 mem] show ?case .
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  from bmk_comb.IH(1)[OF bmk_comb.prems] have b1: "bderiv N r' (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g)" .
  from bmk_comb.IH(2)[OF bmk_comb.prems] have b2: "bderiv N r' (\<Delta>, mk_eq \<sigma> a b)" .
  from Sequent_r_mono_r[OF bmk_comb.prems] bmk_comb.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.bmk_comb[OF b1 b2 mem] show ?case .
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  from babs.IH[OF babs.prems] have b1: "bderiv N r' (\<Gamma>, mk_eq \<tau> s t)" .
  from Sequent_r_mono_r[OF babs.prems] babs.hyps(4)
  have mem: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N \<Sigma> r'"
    by blast
  from bderiv.babs[OF b1 babs.hyps(2) babs.hyps(3) mem] show ?case .
next
  case (bbeta \<sigma> b \<tau> x)
  from Sequent_r_mono_r[OF bbeta.prems] bbeta.hyps(2)
  have mem: "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r N \<Sigma> r'"
    by blast
  from bderiv.bbeta[OF bbeta.hyps(1) mem] show ?case .
next
  case (bassm p)
  from Sequent_r_mono_r[OF bassm.prems] bassm.hyps(2)
  have mem: "({p}, p) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.bassm[OF bassm.hyps(1) mem] show ?case .
next
  case (beq_mp \<Gamma> p q \<Delta>)
  from beq_mp.IH(1)[OF beq_mp.prems] have b1: "bderiv N r' (\<Gamma>, mk_eq boolT p q)" .
  from beq_mp.IH(2)[OF beq_mp.prems] have b2: "bderiv N r' (\<Delta>, p)" .
  from Sequent_r_mono_r[OF beq_mp.prems] beq_mp.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, q) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.beq_mp[OF b1 b2 mem] show ?case .
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  from bdeduct_antisym.IH(1)[OF bdeduct_antisym.prems] have b1: "bderiv N r' (\<Gamma>, p)" .
  from bdeduct_antisym.IH(2)[OF bdeduct_antisym.prems] have b2: "bderiv N r' (\<Delta>, q)" .
  from Sequent_r_mono_r[OF bdeduct_antisym.prems] bdeduct_antisym.hyps(3)
  have mem: "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.bdeduct_antisym[OF b1 b2 mem] show ?case .
next
  case (binst_type \<Gamma> c \<theta>)
  from binst_type.IH[OF binst_type.prems] have b1: "bderiv N r' (\<Gamma>, c)" .
  from Sequent_r_mono_r[OF binst_type.prems] binst_type.hyps(3)
  have mem: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.binst_type[OF b1 binst_type.hyps(2) mem] show ?case .
next
  case (baxiom p)
  from Sequent_r_mono_r[OF baxiom.prems] baxiom.hyps(2)
  have mem: "({}, p) \<in> Sequent_r N \<Sigma> r'" by blast
  from bderiv.baxiom[OF baxiom.hyps(1) mem] show ?case .
qed

lemma bderiv_mono_r: "r \<le> r' \<Longrightarrow> bderiv N r (\<Gamma>, c) \<Longrightarrow> bderiv N r' (\<Gamma>, c)"
  using bderiv_mono_r_aux[of N r "(\<Gamma>, c)" r'] by simp

lemma bderiv_mono_N_aux: "bderiv N r p \<Longrightarrow> N \<subseteq> N' \<Longrightarrow> bderiv N' r p"
proof (induction arbitrary: N' rule: bderiv.induct)
  case (brefl t \<tau>)
  from Sequent_r_mono_N[OF brefl.prems] brefl.hyps(2)
  have mem: "({}, mk_eq \<tau> t t) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.brefl[OF brefl.hyps(1) mem] show ?case .
next
  case (btrans \<Gamma> \<tau> s t \<Delta> u)
  from btrans.IH(1)[OF btrans.prems] have b1: "bderiv N' r (\<Gamma>, mk_eq \<tau> s t)" .
  from btrans.IH(2)[OF btrans.prems] have b2: "bderiv N' r (\<Delta>, mk_eq \<tau> t u)" .
  from Sequent_r_mono_N[OF btrans.prems] btrans.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.btrans[OF b1 b2 mem] show ?case .
next
  case (bmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  from bmk_comb.IH(1)[OF bmk_comb.prems] have b1: "bderiv N' r (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g)" .
  from bmk_comb.IH(2)[OF bmk_comb.prems] have b2: "bderiv N' r (\<Delta>, mk_eq \<sigma> a b)" .
  from Sequent_r_mono_N[OF bmk_comb.prems] bmk_comb.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.bmk_comb[OF b1 b2 mem] show ?case .
next
  case (babs \<Gamma> \<tau> s t \<sigma> x)
  from babs.IH[OF babs.prems] have b1: "bderiv N' r (\<Gamma>, mk_eq \<tau> s t)" .
  from Sequent_r_mono_N[OF babs.prems] babs.hyps(4)
  have mem: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N' \<Sigma> r"
    by blast
  from bderiv.babs[OF b1 babs.hyps(2) babs.hyps(3) mem] show ?case .
next
  case (bbeta \<sigma> b \<tau> x)
  from Sequent_r_mono_N[OF bbeta.prems] bbeta.hyps(2)
  have mem: "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r N' \<Sigma> r"
    by blast
  from bderiv.bbeta[OF bbeta.hyps(1) mem] show ?case .
next
  case (bassm p)
  from Sequent_r_mono_N[OF bassm.prems] bassm.hyps(2)
  have mem: "({p}, p) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.bassm[OF bassm.hyps(1) mem] show ?case .
next
  case (beq_mp \<Gamma> p q \<Delta>)
  from beq_mp.IH(1)[OF beq_mp.prems] have b1: "bderiv N' r (\<Gamma>, mk_eq boolT p q)" .
  from beq_mp.IH(2)[OF beq_mp.prems] have b2: "bderiv N' r (\<Delta>, p)" .
  from Sequent_r_mono_N[OF beq_mp.prems] beq_mp.hyps(3)
  have mem: "(\<Gamma> \<union> \<Delta>, q) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.beq_mp[OF b1 b2 mem] show ?case .
next
  case (bdeduct_antisym \<Gamma> p \<Delta> q)
  from bdeduct_antisym.IH(1)[OF bdeduct_antisym.prems] have b1: "bderiv N' r (\<Gamma>, p)" .
  from bdeduct_antisym.IH(2)[OF bdeduct_antisym.prems] have b2: "bderiv N' r (\<Delta>, q)" .
  from Sequent_r_mono_N[OF bdeduct_antisym.prems] bdeduct_antisym.hyps(3)
  have mem: "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.bdeduct_antisym[OF b1 b2 mem] show ?case .
next
  case (binst_type \<Gamma> c \<theta>)
  from binst_type.IH[OF binst_type.prems] have b1: "bderiv N' r (\<Gamma>, c)" .
  from Sequent_r_mono_N[OF binst_type.prems] binst_type.hyps(3)
  have mem: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.binst_type[OF b1 binst_type.hyps(2) mem] show ?case .
next
  case (baxiom p)
  from Sequent_r_mono_N[OF baxiom.prems] baxiom.hyps(2)
  have mem: "({}, p) \<in> Sequent_r N' \<Sigma> r" by blast
  from bderiv.baxiom[OF baxiom.hyps(1) mem] show ?case .
qed

lemma bderiv_mono_N: "N \<subseteq> N' \<Longrightarrow> bderiv N r (\<Gamma>, c) \<Longrightarrow> bderiv N' r (\<Gamma>, c)"
  using bderiv_mono_N_aux[of N r "(\<Gamma>, c)" N'] by simp

subsection \<open>The \<open>inst\<close> rule never fires\<close>

text \<open>
  A single function @{term \<sigma>} of type @{typ "name \<Rightarrow> ty \<Rightarrow> tm"} can never satisfy
  @{term "\<forall>x \<tau>. has_type \<Sigma> [] (\<sigma> x \<tau>) \<tau>"}: instantiating at the ill-formed type
  @{term "TyApp ''bool'' [TyVar ''a'']"} (arity mismatch against @{term "sig_ok \<Sigma>"}'s
  @{term "tyar \<Sigma> ''bool'' = Some 0"}) would force that type to be well-formed, which it is not.
  Consequently the @{text inst} rule of @{const derivable} never applies, and every derivable
  sequent is already derivable without it.
\<close>

lemma inst_premise_unsat: "\<not> (\<forall>(x :: name) \<tau>. has_type \<Sigma> [] (\<sigma> x \<tau>) \<tau>)"
proof
  assume all: "\<forall>x \<tau>. has_type \<Sigma> [] (\<sigma> x \<tau>) \<tau>"
  define \<tau>0 :: ty where "\<tau>0 = TyApp ''bool'' [TyVar ''a'']"
  from all have "has_type \<Sigma> [] (\<sigma> '''' \<tau>0) \<tau>0" by blast
  from has_type_wf[OF sig_ok _ this] have "wf_ty \<Sigma> \<tau>0" by simp
  moreover have "\<not> wf_ty \<Sigma> \<tau>0" unfolding \<tau>0_def using sig_ok_bool[OF sig_ok] by simp
  ultimately show False by contradiction
qed

subsection \<open>Hypotheses of a derivable sequent are finite\<close>

lemma derivable_finite_hyps: "derivable \<Gamma> c \<Longrightarrow> finite \<Gamma>"
  by (induction rule: derivable.induct) auto

subsection \<open>Every well-typed finite sequent lies in some region\<close>

lemma Sequent_r_exists:
  assumes "finite \<Gamma>" and "\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT" and "has_type \<Sigma> [] c boolT"
  shows "\<exists>N r. finite N \<and> (\<Gamma>, c) \<in> Sequent_r N \<Sigma> r"
proof -
  define g :: "tm \<Rightarrow> nat" where "g t = max (tm_size t) (tm_maxbv t)" for t
  define N where "N = tm_names c \<union> (\<Union>p\<in>\<Gamma>. tm_names p)"
  define r where "r = Max (insert (g c) (g ` \<Gamma>))"
  have finN: "finite N" unfolding N_def using assms(1) by auto
  have finGr: "finite (insert (g c) (g ` \<Gamma>))" using assms(1) by auto
  have rc: "g c \<le> r" unfolding r_def using finGr by (intro Max_ge) auto
  have c_mem: "c \<in> Tm_wt N \<Sigma> r"
  proof -
    from has_type_wf_tm_ty[OF assms(3)] have wf: "wf_tm_ty \<Sigma> c" .
    have nm: "tm_names c \<subseteq> N" unfolding N_def by auto
    from Tm_exhaust[OF wf nm] have mem0: "c \<in> Tm N \<Sigma> (g c)" unfolding g_def .
    from Tm_mono_r[OF rc] mem0 have "c \<in> Tm N \<Sigma> r" by blast
    with typeof_iff_has_type assms(3) show ?thesis unfolding Tm_wt_def by auto
  qed
  have hyps_mem: "\<Gamma> \<subseteq> Tm_wt N \<Sigma> r"
  proof
    fix p assume p: "p \<in> \<Gamma>"
    from assms(2) p have hp: "has_type \<Sigma> [] p boolT" by blast
    from has_type_wf_tm_ty[OF hp] have wf: "wf_tm_ty \<Sigma> p" .
    have nm: "tm_names p \<subseteq> N" unfolding N_def using p by auto
    from Tm_exhaust[OF wf nm] have mem0: "p \<in> Tm N \<Sigma> (g p)" unfolding g_def .
    have rp: "g p \<le> r" unfolding r_def using finGr p by (intro Max_ge) auto
    from Tm_mono_r[OF rp] mem0 have "p \<in> Tm N \<Sigma> r" by blast
    with typeof_iff_has_type hp show "p \<in> Tm_wt N \<Sigma> r" unfolding Tm_wt_def by auto
  qed
  from hyps_mem c_mem have "(\<Gamma>, c) \<in> Sequent_r N \<Sigma> r" unfolding Sequent_r_def by auto
  with finN show ?thesis by blast
qed

subsection \<open>Lifting facts to a larger common region\<close>

lemma bderiv_lift: "bderiv N0 r0 (\<Gamma>, c) \<Longrightarrow> N0 \<subseteq> N \<Longrightarrow> r0 \<le> r \<Longrightarrow> bderiv N r (\<Gamma>, c)"
  using bderiv_mono_N bderiv_mono_r by blast

lemma Sequent_r_lift: "(\<Gamma>, c) \<in> Sequent_r N0 \<Sigma> r0 \<Longrightarrow> N0 \<subseteq> N \<Longrightarrow> r0 \<le> r \<Longrightarrow> (\<Gamma>, c) \<in> Sequent_r N \<Sigma> r"
proof -
  assume mem: "(\<Gamma>, c) \<in> Sequent_r N0 \<Sigma> r0" and n: "N0 \<subseteq> N" and r: "r0 \<le> r"
  from Sequent_r_mono_N[OF n] mem have "(\<Gamma>, c) \<in> Sequent_r N \<Sigma> r0" by auto
  with Sequent_r_mono_r[OF r] show "(\<Gamma>, c) \<in> Sequent_r N \<Sigma> r" by auto
qed

subsection \<open>Completeness\<close>

text \<open>
  For each derivable sequent we exhibit a finite @{term N} and a bound @{term r}: for the axioms
  of @{const derivable} (\<open>refl\<close>, \<open>beta\<close>, \<open>assm\<close>, \<open>axiom\<close>) this is @{term Sequent_r_exists} applied
  to the sequent itself; for the rules with one or two derivable premises, the regions of the
  premises (given by the induction hypothesis) and of the new conclusion (again via
  @{term Sequent_r_exists}) are combined by union (on @{term N}) and @{term max} (on @{term r})
  and all three facts are lifted to the common region with @{term bderiv_lift} /
  @{term Sequent_r_lift}.  The \<open>inst\<close> case is vacuous by @{thm inst_premise_unsat}.
\<close>

lemma derivable_bderiv_ex: "derivable \<Gamma> c \<Longrightarrow> \<exists>N r. finite N \<and> bderiv N r (\<Gamma>, c)"
proof (induction rule: derivable.induct)
  case (refl t \<tau>)
  from derivable_closed[OF derivable.refl[OF refl.hyps]]
  have hc: "has_type \<Sigma> [] (mk_eq \<tau> t t) boolT" .
  have fin_empty: "finite ({} :: tm set)" by simp
  have typed_empty: "\<forall>p\<in>({} :: tm set). has_type \<Sigma> [] p boolT" by simp
  from Sequent_r_exists[OF fin_empty typed_empty hc]
  obtain N r where fn: "finite N" and mem: "({}, mk_eq \<tau> t t) \<in> Sequent_r N \<Sigma> r" by blast
  from bderiv.brefl[OF refl.hyps mem] fn show ?case by blast
next
  case (trans \<Gamma> \<tau> s t \<Delta> u)
  from trans.IH(1) obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, mk_eq \<tau> s t)" by blast
  from trans.IH(2) obtain N2 r2 where fn2: "finite N2" and b2: "bderiv N2 r2 (\<Delta>, mk_eq \<tau> t u)" by blast
  from derivable_finite_hyps[OF trans.hyps(1)] derivable_finite_hyps[OF trans.hyps(2)]
  have fg: "finite \<Gamma>" and fd: "finite \<Delta>" by auto
  from derivable_typed[OF trans.hyps(1)] derivable_typed[OF trans.hyps(2)]
  have hyps_typed: "\<forall>z\<in>\<Gamma> \<union> \<Delta>. has_type \<Sigma> [] z boolT" by auto
  from derivable_closed[OF derivable.trans[OF trans.hyps(1) trans.hyps(2)]]
  have hc: "has_type \<Sigma> [] (mk_eq \<tau> s u) boolT" .
  from Sequent_r_exists[OF finite_UnI[OF fg fd] hyps_typed hc]
  obtain N0 r0 where fn0: "finite N0" and mem0: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_r N0 \<Sigma> r0" by blast
  define N where "N = N1 \<union> N2 \<union> N0"
  define r where "r = max r1 (max r2 r0)"
  have fn: "finite N" unfolding N_def using fn1 fn2 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN2: "N2 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr2: "r2 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, mk_eq \<tau> s t)" .
  from bderiv_lift[OF b2 sN2 sr2] have b2': "bderiv N r (\<Delta>, mk_eq \<tau> t u)" .
  from Sequent_r_lift[OF mem0 sN0 sr0] have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.btrans[OF b1' b2' mem] fn show ?case by blast
next
  case (mk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  from mk_comb.IH(1) obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g)"
    by blast
  from mk_comb.IH(2) obtain N2 r2 where fn2: "finite N2" and b2: "bderiv N2 r2 (\<Delta>, mk_eq \<sigma> a b)" by blast
  from derivable_finite_hyps[OF mk_comb.hyps(1)] derivable_finite_hyps[OF mk_comb.hyps(2)]
  have fg: "finite \<Gamma>" and fd: "finite \<Delta>" by auto
  from derivable_typed[OF mk_comb.hyps(1)] derivable_typed[OF mk_comb.hyps(2)]
  have hyps_typed: "\<forall>z\<in>\<Gamma> \<union> \<Delta>. has_type \<Sigma> [] z boolT" by auto
  from derivable_closed[OF derivable.mk_comb[OF mk_comb.hyps(1) mk_comb.hyps(2)]]
  have hc: "has_type \<Sigma> [] (mk_eq \<tau> (App f a) (App g b)) boolT" .
  from Sequent_r_exists[OF finite_UnI[OF fg fd] hyps_typed hc]
  obtain N0 r0 where fn0: "finite N0" and mem0: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N0 \<Sigma> r0"
    by blast
  define N where "N = N1 \<union> N2 \<union> N0"
  define r where "r = max r1 (max r2 r0)"
  have fn: "finite N" unfolding N_def using fn1 fn2 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN2: "N2 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr2: "r2 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g)" .
  from bderiv_lift[OF b2 sN2 sr2] have b2': "bderiv N r (\<Delta>, mk_eq \<sigma> a b)" .
  from Sequent_r_lift[OF mem0 sN0 sr0] have mem: "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.bmk_comb[OF b1' b2' mem] fn show ?case by blast
next
  case (abs \<Gamma> \<tau> s t \<sigma> x)
  from abs.IH obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, mk_eq \<tau> s t)" by blast
  from derivable_finite_hyps[OF abs.hyps(1)] have fg: "finite \<Gamma>" .
  from derivable_typed[OF abs.hyps(1)] have hyps_typed: "\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT" by simp
  from derivable_closed[OF derivable.abs[OF abs.hyps(1) abs.hyps(2) abs.hyps(3)]]
  have hc: "has_type \<Sigma> [] (mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) boolT" .
  from Sequent_r_exists[OF fg hyps_typed hc]
  obtain N0 r0 where fn0: "finite N0"
    and mem0: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N0 \<Sigma> r0"
    by blast
  define N where "N = N1 \<union> N0"
  define r where "r = max r1 r0"
  have fn: "finite N" unfolding N_def using fn1 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, mk_eq \<tau> s t)" .
  from Sequent_r_lift[OF mem0 sN0 sr0]
  have mem: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.babs[OF b1' abs.hyps(2) abs.hyps(3) mem] fn show ?case by blast
next
  case (beta \<sigma> b \<tau> x)
  from derivable_closed[OF derivable.beta[OF beta.hyps]]
  have hc: "has_type \<Sigma> [] (mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) boolT" .
  have fin_empty: "finite ({} :: tm set)" by simp
  have typed_empty: "\<forall>p\<in>({} :: tm set). has_type \<Sigma> [] p boolT" by simp
  from Sequent_r_exists[OF fin_empty typed_empty hc]
  obtain N r where fn: "finite N"
    and mem: "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r N \<Sigma> r"
    by blast
  from bderiv.bbeta[OF beta.hyps mem] fn show ?case by blast
next
  case (assm p)
  from assm.hyps have hc: "has_type \<Sigma> [] p boolT" .
  have fin_p: "finite ({p} :: tm set)" by simp
  have typed_p: "\<forall>q\<in>({p} :: tm set). has_type \<Sigma> [] q boolT" using assm.hyps by simp
  from Sequent_r_exists[OF fin_p typed_p hc]
  obtain N r where fn: "finite N" and mem: "({p}, p) \<in> Sequent_r N \<Sigma> r" by blast
  from bderiv.bassm[OF assm.hyps mem] fn show ?case by blast
next
  case (eq_mp \<Gamma> p q \<Delta>)
  from eq_mp.IH(1) obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, mk_eq boolT p q)" by blast
  from eq_mp.IH(2) obtain N2 r2 where fn2: "finite N2" and b2: "bderiv N2 r2 (\<Delta>, p)" by blast
  from derivable_finite_hyps[OF eq_mp.hyps(1)] derivable_finite_hyps[OF eq_mp.hyps(2)]
  have fg: "finite \<Gamma>" and fd: "finite \<Delta>" by auto
  from derivable_typed[OF eq_mp.hyps(1)] derivable_typed[OF eq_mp.hyps(2)]
  have hyps_typed: "\<forall>z\<in>\<Gamma> \<union> \<Delta>. has_type \<Sigma> [] z boolT" by auto
  from derivable_closed[OF derivable.eq_mp[OF eq_mp.hyps(1) eq_mp.hyps(2)]]
  have hc: "has_type \<Sigma> [] q boolT" .
  from Sequent_r_exists[OF finite_UnI[OF fg fd] hyps_typed hc]
  obtain N0 r0 where fn0: "finite N0" and mem0: "(\<Gamma> \<union> \<Delta>, q) \<in> Sequent_r N0 \<Sigma> r0" by blast
  define N where "N = N1 \<union> N2 \<union> N0"
  define r where "r = max r1 (max r2 r0)"
  have fn: "finite N" unfolding N_def using fn1 fn2 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN2: "N2 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr2: "r2 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, mk_eq boolT p q)" .
  from bderiv_lift[OF b2 sN2 sr2] have b2': "bderiv N r (\<Delta>, p)" .
  from Sequent_r_lift[OF mem0 sN0 sr0] have mem: "(\<Gamma> \<union> \<Delta>, q) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.beq_mp[OF b1' b2' mem] fn show ?case by blast
next
  case (deduct_antisym \<Gamma> p \<Delta> q)
  from deduct_antisym.IH(1) obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, p)" by blast
  from deduct_antisym.IH(2) obtain N2 r2 where fn2: "finite N2" and b2: "bderiv N2 r2 (\<Delta>, q)" by blast
  from derivable_finite_hyps[OF deduct_antisym.hyps(1)] derivable_finite_hyps[OF deduct_antisym.hyps(2)]
  have fg: "finite \<Gamma>" and fd: "finite \<Delta>" by auto
  have fgd: "finite ((\<Gamma> - {q}) \<union> (\<Delta> - {p}))" using fg fd by simp
  from derivable_typed[OF deduct_antisym.hyps(1)] derivable_typed[OF deduct_antisym.hyps(2)]
  have hyps_typed: "\<forall>z\<in>(\<Gamma> - {q}) \<union> (\<Delta> - {p}). has_type \<Sigma> [] z boolT" by auto
  from derivable_closed[OF derivable.deduct_antisym[OF deduct_antisym.hyps(1) deduct_antisym.hyps(2)]]
  have hc: "has_type \<Sigma> [] (mk_eq boolT p q) boolT" .
  from Sequent_r_exists[OF fgd hyps_typed hc]
  obtain N0 r0 where fn0: "finite N0"
    and mem0: "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_r N0 \<Sigma> r0" by blast
  define N where "N = N1 \<union> N2 \<union> N0"
  define r where "r = max r1 (max r2 r0)"
  have fn: "finite N" unfolding N_def using fn1 fn2 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN2: "N2 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr2: "r2 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, p)" .
  from bderiv_lift[OF b2 sN2 sr2] have b2': "bderiv N r (\<Delta>, q)" .
  from Sequent_r_lift[OF mem0 sN0 sr0]
  have mem: "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.bdeduct_antisym[OF b1' b2' mem] fn show ?case by blast
next
  case (inst_type \<Gamma> c \<theta>)
  from inst_type.IH obtain N1 r1 where fn1: "finite N1" and b1: "bderiv N1 r1 (\<Gamma>, c)" by blast
  from derivable_finite_hyps[OF inst_type.hyps(1)] have fg: "finite \<Gamma>" .
  from derivable_typed[OF inst_type.hyps(1)] have hyps_typed: "\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT" by simp
  from derivable.inst_type[OF inst_type.hyps(1) inst_type.hyps(2)]
  have d: "derivable (tinst \<theta> ` \<Gamma>) (tinst \<theta> c)" .
  from derivable_typed[OF d] have hyps_typed': "\<forall>q\<in>tinst \<theta> ` \<Gamma>. has_type \<Sigma> [] q boolT" by simp
  from derivable_closed[OF d] have hc: "has_type \<Sigma> [] (tinst \<theta> c) boolT" .
  have fgd: "finite (tinst \<theta> ` \<Gamma>)" using fg by simp
  from Sequent_r_exists[OF fgd hyps_typed' hc]
  obtain N0 r0 where fn0: "finite N0" and mem0: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_r N0 \<Sigma> r0" by blast
  define N where "N = N1 \<union> N0"
  define r where "r = max r1 r0"
  have fn: "finite N" unfolding N_def using fn1 fn0 by simp
  have sN1: "N1 \<subseteq> N" and sN0: "N0 \<subseteq> N" unfolding N_def by auto
  have sr1: "r1 \<le> r" and sr0: "r0 \<le> r" unfolding r_def by auto
  from bderiv_lift[OF b1 sN1 sr1] have b1': "bderiv N r (\<Gamma>, c)" .
  from Sequent_r_lift[OF mem0 sN0 sr0] have mem: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_r N \<Sigma> r" .
  from bderiv.binst_type[OF b1' inst_type.hyps(2) mem] fn show ?case by blast
next
  case (inst \<Gamma> c \<sigma>)
  from inst_premise_unsat inst.hyps(2) have False by blast
  then show ?case ..
next
  case (axiom p)
  from derivable_closed[OF derivable.axiom[OF axiom.hyps]] have hc: "has_type \<Sigma> [] p boolT" .
  have fin_empty: "finite ({} :: tm set)" by simp
  have typed_empty: "\<forall>q\<in>({} :: tm set). has_type \<Sigma> [] q boolT" by simp
  from Sequent_r_exists[OF fin_empty typed_empty hc]
  obtain N r where fn: "finite N" and mem: "({}, p) \<in> Sequent_r N \<Sigma> r" by blast
  from bderiv.baxiom[OF axiom.hyps mem] fn show ?case by blast
qed

subsection \<open>The main theorem\<close>

theorem derivable_iff_bderiv: "derivable \<Gamma> c \<longleftrightarrow> (\<exists>N r. finite N \<and> bderiv N r (\<Gamma>, c))"
proof
  assume "derivable \<Gamma> c"
  then show "\<exists>N r. finite N \<and> bderiv N r (\<Gamma>, c)" by (rule derivable_bderiv_ex)
next
  assume "\<exists>N r. finite N \<and> bderiv N r (\<Gamma>, c)"
  then obtain N r where "bderiv N r (\<Gamma>, c)" by blast
  then show "derivable \<Gamma> c" by (rule bderiv_sound)
qed





end

end
