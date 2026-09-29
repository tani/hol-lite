theory HOL_Lite_L3
  imports HOL_Lite_Kernel HOL_Lite_L1
begin

section \<open>Finite representatives for type instantiation\<close>

text \<open>
  This theory studies the CLIPPED @{text inst_type} rule of the kernel: given a wf-total type
  substitution @{term \<theta>} (@{term "\<forall>a. wf_ty \<Sigma> (\<theta> a)"}) whose instantiated conclusion (and
  hypotheses) happen to land back in the bounded region @{term "Tm N \<Sigma> r"}, we show that
  @{term \<theta>} may be replaced, without changing the instantiated conclusion or hypotheses, by a
  substitution that depends only on the (finite) set of type variables actually occurring in the
  term(s) being instantiated, and whose values on that finite set already lie in the finite set
  @{term "Ty N \<Sigma> r"}. This is the key finiteness fact needed to only ever consider finitely many
  distinct instances of @{text inst_type} when restricting the kernel to a bounded search space;
  no closure theorem is claimed.
\<close>

subsection \<open>Type variables occurring in types and terms\<close>

text \<open>
  @{const ty_names}/@{const tm_names} from \<open>HOL_Lite_L1\<close> collect ALL names (type
  constructors, constants, free variables) occurring in a type/term. Here we need the strictly
  smaller set of type VARIABLE names, i.e. the domain on which a type substitution @{term \<theta>} can
  possibly affect the type/term.
\<close>

fun ty_tyvars :: "ty \<Rightarrow> name set" where
  "ty_tyvars (TyVar a) = {a}"
| "ty_tyvars (TyApp c ts) = \<Union>(set (map ty_tyvars ts))"

fun tm_tyvars :: "tm \<Rightarrow> name set" where
  "tm_tyvars (Fv x \<tau>) = ty_tyvars \<tau>"
| "tm_tyvars (Bv i) = {}"
| "tm_tyvars (Cst c \<tau>) = ty_tyvars \<tau>"
| "tm_tyvars (App f a) = tm_tyvars f \<union> tm_tyvars a"
| "tm_tyvars (Abs \<tau> b) = ty_tyvars \<tau> \<union> tm_tyvars b"

lemma finite_ty_tyvars [simp]: "finite (ty_tyvars \<tau>)"
  by (induction \<tau> rule: ty.induct) auto

lemma finite_tm_tyvars [simp]: "finite (tm_tyvars t)"
  by (induction t rule: tm.induct) auto

subsection \<open>Substitution and instantiation depend only on the type variables occurring\<close>

lemma tsubst_cong:
  assumes "\<And>a. a \<in> ty_tyvars \<tau> \<Longrightarrow> \<theta> a = \<theta>' a"
  shows "tsubst \<theta> \<tau> = tsubst \<theta>' \<tau>"
  using assms
proof (induction \<tau> rule: ty.induct)
  case (TyVar a)
  then show ?case by simp
next
  case (TyApp c ts)
  have ball: "\<forall>t\<in>set ts. tsubst \<theta> t = tsubst \<theta>' t"
  proof
    fix t assume t: "t \<in> set ts"
    have "\<And>a. a \<in> ty_tyvars t \<Longrightarrow> \<theta> a = \<theta>' a"
    proof -
      fix a assume "a \<in> ty_tyvars t"
      with t have "a \<in> ty_tyvars (TyApp c ts)" by auto
      with TyApp.prems show "\<theta> a = \<theta>' a" by blast
    qed
    with TyApp.IH t show "tsubst \<theta> t = tsubst \<theta>' t" by blast
  qed
  have "map (tsubst \<theta>) ts = map (tsubst \<theta>') ts"
  proof (rule map_cong[OF refl])
    fix t assume "t \<in> set ts"
    with ball show "tsubst \<theta> t = tsubst \<theta>' t" by blast
  qed
  then show ?case by simp
qed

lemma tinst_cong:
  assumes "\<And>a. a \<in> tm_tyvars t \<Longrightarrow> \<theta> a = \<theta>' a"
  shows "tinst \<theta> t = tinst \<theta>' t"
  using assms
proof (induction t rule: tm.induct)
  case (Fv x \<tau>)
  from Fv.prems have "\<And>a. a \<in> ty_tyvars \<tau> \<Longrightarrow> \<theta> a = \<theta>' a" by simp
  from tsubst_cong[OF this] show ?case by simp
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  from Cst.prems have "\<And>a. a \<in> ty_tyvars \<tau> \<Longrightarrow> \<theta> a = \<theta>' a" by simp
  from tsubst_cong[OF this] show ?case by simp
next
  case (App f t)
  from App.prems have hf: "\<And>a. a \<in> tm_tyvars f \<Longrightarrow> \<theta> a = \<theta>' a"
    and ht: "\<And>a. a \<in> tm_tyvars t \<Longrightarrow> \<theta> a = \<theta>' a" by auto
  from App.IH(1)[OF hf] App.IH(2)[OF ht] show ?case by simp
next
  case (Abs \<tau> b)
  from Abs.prems have \<tau>eq: "\<And>a. a \<in> ty_tyvars \<tau> \<Longrightarrow> \<theta> a = \<theta>' a"
    and beq: "\<And>a. a \<in> tm_tyvars b \<Longrightarrow> \<theta> a = \<theta>' a" by auto
  from tsubst_cong[OF \<tau>eq] Abs.IH[OF beq] show ?case by simp
qed

subsection \<open>Downward closure of the type search space under immediate arguments\<close>

text \<open>
  If @{term "TyApp c ts"} lies in the bounded region @{term "Ty N \<Sigma> r"}, so does every immediate
  argument @{term t} of @{term ts}: well-formedness, the size bound and the name bound are all
  inherited from @{term "TyApp c ts"} to its immediate arguments (@{const ty_size} strictly
  decreases, so the same bound @{term r} still suffices).
\<close>

lemma Ty_TyApp_argD:
  assumes "TyApp c ts \<in> Ty N \<Sigma> r" and "t \<in> set ts"
  shows "t \<in> Ty N \<Sigma> r"
proof -
  from assms(1) have wf: "wf_ty \<Sigma> (TyApp c ts)" and sz: "ty_size (TyApp c ts) \<le> r"
    and nm: "ty_names (TyApp c ts) \<subseteq> N"
    by (auto simp: Ty_def)
  from wf assms(2) have wft: "wf_ty \<Sigma> t" by auto
  have "ty_size t \<le> sum_list (map ty_size ts)"
    using assms(2) by (induction ts) auto
  with sz have szt: "ty_size t \<le> r" by simp
  from nm assms(2) have nmt: "ty_names t \<subseteq> N" by auto
  from wft szt nmt show ?thesis by (rule Ty_memI)
qed

subsection \<open>Values of the substitution on occurring type variables lie in the region\<close>

text \<open>
  If @{term "tsubst \<theta> \<tau>"} lies in @{term "Ty N \<Sigma> r"} and @{term a} occurs (as a type variable) in
  @{term \<tau>}, then @{term "\<theta> a"} itself lies in @{term "Ty N \<Sigma> r"}: @{term "\<theta> a"} is either equal
  to @{term "tsubst \<theta> \<tau>"} (if @{term "\<tau> = TyVar a"}) or is buried as the substituted image of
  some immediate argument of a @{const TyApp}, and @{thm Ty_TyApp_argD} lets us descend.
\<close>

lemma ty_tyvars_tsubst_mem:
  assumes "tsubst \<theta> \<tau> \<in> Ty N \<Sigma> r" and "a \<in> ty_tyvars \<tau>"
  shows "\<theta> a \<in> Ty N \<Sigma> r"
  using assms
proof (induction \<tau> rule: ty.induct)
  case (TyVar b)
  then show ?case by simp
next
  case (TyApp c ts)
  from TyApp.prems(2) obtain t where t: "t \<in> set ts" and at: "a \<in> ty_tyvars t" by auto
  from TyApp.prems(1) have "TyApp c (map (tsubst \<theta>) ts) \<in> Ty N \<Sigma> r" by simp
  moreover from t have "tsubst \<theta> t \<in> set (map (tsubst \<theta>) ts)" by simp
  ultimately have "tsubst \<theta> t \<in> Ty N \<Sigma> r" using Ty_TyApp_argD by blast
  with TyApp.IH t at show ?case by blast
qed

subsection \<open>Finite representatives for @{text inst_type}\<close>

text \<open>
  The syntactic well-formedness predicate @{const wf_tm} recurses through @{const App}/@{const
  Abs} and requires EVERY type annotation occurring anywhere in a term (at an @{const Fv}, @{const
  Cst} or @{const Abs} node) to lie directly in @{term "Ty N \<Sigma> r"} -- no annotation is ever
  ``erased'' by @{const tinst}, which only ever substitutes inside such annotations. Hence, if the
  instantiated term @{term "tinst \<theta> c"} is syntactically well-formed for the region @{term N},
  @{term \<Sigma>}, @{term r}, then for every type variable @{term a} occurring in @{term c}, the value
  @{term "\<theta> a"} lies in @{term "Ty N \<Sigma> r"} (via @{thm ty_tyvars_tsubst_mem} applied at the
  annotation node where @{term a} occurs). This is the strongest true version of the claim: no
  extra hypothesis on @{term \<theta>}, @{term c}, @{term N}, @{term \<Sigma>}, @{term r} is needed beyond
  @{term "wf_tm N \<Sigma> r (tinst \<theta> c)"}, and no counterexample arises because @{const tinst} never
  drops a type annotation.
\<close>

lemma inst_type_finite_rep_aux:
  assumes "wf_tm N \<Sigma> r (tinst \<theta> c)" and "a \<in> tm_tyvars c"
  shows "\<theta> a \<in> Ty N \<Sigma> r"
  using assms
proof (induction c rule: tm.induct)
  case (Fv x \<tau>)
  then show ?case using ty_tyvars_tsubst_mem by auto
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  then show ?case using ty_tyvars_tsubst_mem by auto
next
  case (App f t)
  from App.prems(1) have hf: "wf_tm N \<Sigma> r (tinst \<theta> f)" and ht: "wf_tm N \<Sigma> r (tinst \<theta> t)"
    by simp_all
  from App.prems(2) have "a \<in> tm_tyvars f \<union> tm_tyvars t" by simp
  then show ?case
  proof
    assume "a \<in> tm_tyvars f" with App.IH(1) hf show ?case by blast
  next
    assume "a \<in> tm_tyvars t" with App.IH(2) ht show ?case by blast
  qed
next
  case (Abs \<tau> b)
  from Abs.prems(1) have h1: "tsubst \<theta> \<tau> \<in> Ty N \<Sigma> r" and h2: "wf_tm N \<Sigma> r (tinst \<theta> b)"
    by simp_all
  from Abs.prems(2) have "a \<in> ty_tyvars \<tau> \<union> tm_tyvars b" by simp
  then show ?case
  proof
    assume "a \<in> ty_tyvars \<tau>" with h1 ty_tyvars_tsubst_mem show ?case by blast
  next
    assume "a \<in> tm_tyvars b" with Abs.IH h2 show ?case by blast
  qed
qed

lemma inst_type_finite_rep:
  assumes "tinst \<theta> c \<in> Tm N \<Sigma> r" and "a \<in> tm_tyvars c"
  shows "\<theta> a \<in> Ty N \<Sigma> r"
  using assms Tm_memD inst_type_finite_rep_aux by blast

subsection \<open>Restricting a wf-total substitution to a finite variable set\<close>

text \<open>
  Inside the kernel locale (which fixes an acceptable signature @{term \<Sigma>}, giving @{term "wf_ty \<Sigma>
  boolT"} via the locale assumption @{text sig_ok}), a wf-total substitution @{term \<theta>} can be
  replaced, on any set @{term V} of names, by a substitution that agrees with @{term \<theta>} on
  @{term V} and defaults to @{term boolT} elsewhere; the result is still wf-total.
\<close>
context hol_lite
begin

definition theta_restrict :: "(name \<Rightarrow> ty) \<Rightarrow> name set \<Rightarrow> name \<Rightarrow> ty" where
  "theta_restrict \<theta> V a = (if a \<in> V then \<theta> a else boolT)"

lemma wf_ty_theta_restrict:
  assumes "\<forall>a. wf_ty \<Sigma> (\<theta> a)"
  shows "wf_ty \<Sigma> (theta_restrict \<theta> V a)"
  using assms wf_boolT[OF sig_ok] by (simp add: theta_restrict_def)

lemma tinst_theta_restrict:
  assumes "tm_tyvars c \<subseteq> V"
  shows "tinst (theta_restrict \<theta> V) c = tinst \<theta> c"
proof (rule tinst_cong)
  fix a assume "a \<in> tm_tyvars c"
  with assms show "theta_restrict \<theta> V a = \<theta> a" by (auto simp: theta_restrict_def subset_iff)
qed

subsection \<open>A finite representative set for the range of @{text inst_type} on a fixed conclusion\<close>

text \<open>
  Combining @{thm tinst_theta_restrict} with @{thm inst_type_finite_rep}: within the bounded
  region @{term "Tm N \<Sigma> r"}, the possible instantiated conclusions @{term "tinst \<theta> c"} for a
  wf-total @{term \<theta>} are exactly the same as those obtained from a @{term \<theta>} that is @{term
  boolT} outside @{term "tm_tyvars c"} and valued in the finite set @{term "Ty N \<Sigma> r"} on
  @{term "tm_tyvars c"}. Since @{term "tm_tyvars c"} is finite (@{thm finite_tm_tyvars}) and
  @{term "Ty N \<Sigma> r"} is finite (@{thm finite_Ty}), this pins down the essential, finite degrees
  of freedom of the clipped @{text inst_type} step for a fixed conclusion @{term c}.
\<close>

theorem inst_type_range_eq:
  "{tinst \<theta> c | \<theta>. \<forall>a. wf_ty \<Sigma> (\<theta> a)} \<inter> Tm N \<Sigma> r
   = {tinst \<theta>' c | \<theta>'. (\<forall>a. wf_ty \<Sigma> (\<theta>' a)) \<and> (\<forall>a. a \<notin> tm_tyvars c \<longrightarrow> \<theta>' a = boolT)
                       \<and> (\<forall>a\<in>tm_tyvars c. \<theta>' a \<in> Ty N \<Sigma> r)} \<inter> Tm N \<Sigma> r"
  (is "?L = ?R")
proof (rule equalityI)
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    then obtain \<theta> where x: "x = tinst \<theta> c" and wf\<theta>: "\<forall>a. wf_ty \<Sigma> (\<theta> a)" and mem: "x \<in> Tm N \<Sigma> r"
      by auto
    define \<theta>' where "\<theta>' = theta_restrict \<theta> (tm_tyvars c)"
    have wf\<theta>': "\<forall>a. wf_ty \<Sigma> (\<theta>' a)"
      unfolding \<theta>'_def using wf_ty_theta_restrict[OF wf\<theta>] by blast
    have out: "\<forall>a. a \<notin> tm_tyvars c \<longrightarrow> \<theta>' a = boolT"
      unfolding \<theta>'_def theta_restrict_def by simp
    have eqx: "tinst \<theta>' c = x"
      unfolding \<theta>'_def using tinst_theta_restrict[of c "tm_tyvars c" \<theta>] x by simp
    have inV: "\<forall>a\<in>tm_tyvars c. \<theta>' a \<in> Ty N \<Sigma> r"
    proof
      fix a assume a: "a \<in> tm_tyvars c"
      then have "\<theta>' a = \<theta> a" unfolding \<theta>'_def theta_restrict_def by simp
      moreover from x mem a inst_type_finite_rep have "\<theta> a \<in> Ty N \<Sigma> r" by blast
      ultimately show "\<theta>' a \<in> Ty N \<Sigma> r" by simp
    qed
    from eqx wf\<theta>' out inV mem show "x \<in> ?R" by blast
  qed
next
  show "?R \<subseteq> ?L" by blast
qed

subsection \<open>The same finite representative fact for a hypothesis set image\<close>

text \<open>
  The @{text inst_type} rule instantiates a whole sequent @{term "(\<Gamma>, c)"} at once, i.e. both the
  conclusion @{term c} and every hypothesis in @{term \<Gamma>} are instantiated by the same @{term \<theta>}.
  The finite-representative fact @{thm inst_type_range_eq} above generalizes verbatim to the
  hypothesis-set image @{term "tinst \<theta> ` \<Gamma>"} of a *finite* @{term \<Gamma>} (finiteness of @{term \<Gamma>} is
  proved separately for derivable sequents in \<open>HOL_Lite_L5\<close>, so it always holds for
  hypothesis sets of derivable sequents): only the finitely many type variables occurring
  somewhere in @{term \<Gamma>} (the finite union @{term "(\<Union>p\<in>\<Gamma>. tm_tyvars p)"}) matter, and @{term \<theta>}
  may again be replaced by a variant valued in @{term "Ty N \<Sigma> r"} on that finite set and equal to
  @{term boolT} elsewhere, without changing @{term "tinst \<theta> ` \<Gamma>"}.
\<close>

lemma finite_tm_tyvars_Union: "finite \<Gamma> \<Longrightarrow> finite (\<Union>p\<in>\<Gamma>. tm_tyvars p)"
  by (intro finite_UN_I) auto

theorem inst_type_range_eq_hyps:
  assumes "finite \<Gamma>"
  shows "finite (\<Union>p\<in>\<Gamma>. tm_tyvars p)
       \<and> {tinst \<theta> ` \<Gamma> | \<theta>. \<forall>a. wf_ty \<Sigma> (\<theta> a)} \<inter> Pow (Tm N \<Sigma> r)
         = {tinst \<theta>' ` \<Gamma> | \<theta>'. (\<forall>a. wf_ty \<Sigma> (\<theta>' a))
                              \<and> (\<forall>a. a \<notin> (\<Union>p\<in>\<Gamma>. tm_tyvars p) \<longrightarrow> \<theta>' a = boolT)
                              \<and> (\<forall>a\<in>(\<Union>p\<in>\<Gamma>. tm_tyvars p). \<theta>' a \<in> Ty N \<Sigma> r)} \<inter> Pow (Tm N \<Sigma> r)"
  (is "?F \<and> ?L = ?R")
proof (rule conjI)
  show ?F using assms by (rule finite_tm_tyvars_Union)
next
  show "?L = ?R"
  proof (rule equalityI)
    show "?L \<subseteq> ?R"
    proof
      fix x assume "x \<in> ?L"
      then obtain \<theta> where x: "x = tinst \<theta> ` \<Gamma>" and wf\<theta>: "\<forall>a. wf_ty \<Sigma> (\<theta> a)"
        and mem: "x \<in> Pow (Tm N \<Sigma> r)"
        by auto
      from mem x have himg: "\<forall>p\<in>\<Gamma>. tinst \<theta> p \<in> Tm N \<Sigma> r" by auto
      define \<theta>' where "\<theta>' = theta_restrict \<theta> (\<Union>p\<in>\<Gamma>. tm_tyvars p)"
      have wf\<theta>': "\<forall>a. wf_ty \<Sigma> (\<theta>' a)"
        unfolding \<theta>'_def using wf_ty_theta_restrict[OF wf\<theta>] by blast
      have out: "\<forall>a. a \<notin> (\<Union>p\<in>\<Gamma>. tm_tyvars p) \<longrightarrow> \<theta>' a = boolT"
        unfolding \<theta>'_def theta_restrict_def by simp
      have eqp: "\<And>p. p \<in> \<Gamma> \<Longrightarrow> tinst \<theta>' p = tinst \<theta> p"
        unfolding \<theta>'_def using tinst_theta_restrict[of _ "\<Union>p\<in>\<Gamma>. tm_tyvars p" \<theta>] by blast
      have eqx: "tinst \<theta>' ` \<Gamma> = x"
        unfolding x using eqp by force
      have inV: "\<forall>a\<in>(\<Union>p\<in>\<Gamma>. tm_tyvars p). \<theta>' a \<in> Ty N \<Sigma> r"
      proof
        fix a assume aV: "a \<in> (\<Union>p\<in>\<Gamma>. tm_tyvars p)"
        then obtain p where p: "p \<in> \<Gamma>" and a: "a \<in> tm_tyvars p" by blast
        from aV have "\<theta>' a = \<theta> a" unfolding \<theta>'_def theta_restrict_def by simp
        moreover from himg p have "tinst \<theta> p \<in> Tm N \<Sigma> r" by blast
        with a inst_type_finite_rep have "\<theta> a \<in> Ty N \<Sigma> r" by blast
        ultimately show "\<theta>' a \<in> Ty N \<Sigma> r" by simp
      qed
      from eqx wf\<theta>' out inV mem show "x \<in> ?R" by blast
    qed
  next
    show "?R \<subseteq> ?L" by blast
  qed
qed
end

end
