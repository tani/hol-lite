theory HOL_Lite_Typing
  imports HOL_Lite_Syntax
begin

section \<open>Signatures and typing\<close>

subsection \<open>Signatures and well-formed types\<close>

text \<open>
  A signature assigns arities to type constructors and generic types to constants.
  Both are total maps into @{type option}; @{term None} means ``not declared''.
\<close>

datatype hsig = HSig (tyar: "name \<Rightarrow> nat option") (ctype: "name \<Rightarrow> ty option")

text \<open>A type is well-formed if every constructor is declared and applied to the right number of arguments.\<close>

fun wf_ty :: "hsig \<Rightarrow> ty \<Rightarrow> bool" where
  "wf_ty \<Sigma> (TyVar _) = True"
| "wf_ty \<Sigma> (TyApp c ts) = (tyar \<Sigma> c = Some (length ts) \<and> (\<forall>t\<in>set ts. wf_ty \<Sigma> t))"

text \<open>
  A signature is acceptable if it declares @{text fun}, @{text bool} and the polymorphic
  equality constant, and all declared constant types are well-formed.
\<close>

definition sig_ok :: "hsig \<Rightarrow> bool" where
  "sig_ok \<Sigma> \<longleftrightarrow> tyar \<Sigma> ''fun'' = Some 2 \<and> tyar \<Sigma> ''bool'' = Some 0
     \<and> ctype \<Sigma> ''='' = Some (funT (TyVar ''a'') (funT (TyVar ''a'') boolT))
     \<and> (\<forall>c \<tau>. ctype \<Sigma> c = Some \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau>)"

lemma sig_ok_fun: "sig_ok \<Sigma> \<Longrightarrow> tyar \<Sigma> ''fun'' = Some 2"
  by (simp add: sig_ok_def)

lemma sig_ok_bool: "sig_ok \<Sigma> \<Longrightarrow> tyar \<Sigma> ''bool'' = Some 0"
  by (simp add: sig_ok_def)

lemma sig_ok_eq: "sig_ok \<Sigma> \<Longrightarrow> ctype \<Sigma> ''='' = Some (funT (TyVar ''a'') (funT (TyVar ''a'') boolT))"
  by (simp add: sig_ok_def)

lemma wf_boolT: "sig_ok \<Sigma> \<Longrightarrow> wf_ty \<Sigma> boolT"
  by (simp add: sig_ok_bool)

lemma wf_funT: "sig_ok \<Sigma> \<Longrightarrow> wf_ty \<Sigma> (funT a b) \<longleftrightarrow> wf_ty \<Sigma> a \<and> wf_ty \<Sigma> b"
  by (simp add: sig_ok_fun)

lemma wf_ty_tsubst:
  assumes "wf_ty \<Sigma> \<tau>" and "\<And>a. wf_ty \<Sigma> (\<theta> a)"
  shows "wf_ty \<Sigma> (tsubst \<theta> \<tau>)"
  using assms
proof (induct \<tau> rule: ty.induct)
  case (TyVar a)
  then show ?case by simp
next
  case (TyApp c ts)
  then show ?case by auto
qed

subsection \<open>Typing judgement\<close>

text \<open>
  @{term "has_type \<Sigma> \<Gamma> t \<tau>"}: term @{term t} has type @{term \<tau>}, where @{term \<Gamma>} lists the types
  of the loose bound indices.  A closed well-typed term satisfies @{term "has_type \<Sigma> [] t \<tau>"}.
  Constants carry their instantiated type, which must be an instance of the declared one.
\<close>

inductive has_type :: "hsig \<Rightarrow> ty list \<Rightarrow> tm \<Rightarrow> ty \<Rightarrow> bool" for \<Sigma> where
  Fv:  "wf_ty \<Sigma> \<tau> \<Longrightarrow> has_type \<Sigma> \<Gamma> (Fv x \<tau>) \<tau>"
| Bv:  "i < length \<Gamma> \<Longrightarrow> \<Gamma> ! i = \<tau> \<Longrightarrow> has_type \<Sigma> \<Gamma> (Bv i) \<tau>"
| Cst: "ctype \<Sigma> c = Some \<sigma>0 \<Longrightarrow> wf_ty \<Sigma> \<tau> \<Longrightarrow> (\<exists>\<theta>. tsubst \<theta> \<sigma>0 = \<tau>) \<Longrightarrow> has_type \<Sigma> \<Gamma> (Cst c \<tau>) \<tau>"
| App: "has_type \<Sigma> \<Gamma> f (funT \<sigma> \<tau>) \<Longrightarrow> has_type \<Sigma> \<Gamma> a \<sigma> \<Longrightarrow> has_type \<Sigma> \<Gamma> (App f a) \<tau>"
| Abs: "wf_ty \<Sigma> \<sigma> \<Longrightarrow> has_type \<Sigma> (\<sigma> # \<Gamma>) b \<tau> \<Longrightarrow> has_type \<Sigma> \<Gamma> (Abs \<sigma> b) (funT \<sigma> \<tau>)"

inductive_cases has_type_FvE: "has_type \<Sigma> \<Gamma> (Fv x \<tau>) \<rho>"
inductive_cases has_type_BvE: "has_type \<Sigma> \<Gamma> (Bv i) \<rho>"
inductive_cases has_type_CstE: "has_type \<Sigma> \<Gamma> (Cst c \<tau>) \<rho>"
inductive_cases has_type_AppE: "has_type \<Sigma> \<Gamma> (App f a) \<rho>"
inductive_cases has_type_AbsE: "has_type \<Sigma> \<Gamma> (Abs \<sigma> b) \<rho>"

subsection \<open>Basic properties\<close>

lemma has_type_unique:
  assumes "has_type \<Sigma> \<Gamma> t \<tau>" and "has_type \<Sigma> \<Gamma> t \<tau>'"
  shows "\<tau> = \<tau>'"
  using assms
proof (induction arbitrary: \<tau>' rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  from Fv.prems show ?case by (auto elim: has_type_FvE)
next
  case (Bv i \<Gamma> \<tau>)
  from Bv.prems show ?case using Bv.hyps by (auto elim: has_type_BvE)
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  from Cst.prems show ?case by (auto elim: has_type_CstE)
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  from App.prems obtain \<sigma>' where "has_type \<Sigma> \<Gamma> f (funT \<sigma>' \<tau>')"
    by (auto elim: has_type_AppE)
  then have "funT \<sigma> \<tau> = funT \<sigma>' \<tau>'" by (rule App.IH(1))
  then show ?case by simp
next
  case (Abs \<sigma> \<Gamma> b \<tau>)
  from Abs.prems obtain \<tau>'' where "\<tau>' = funT \<sigma> \<tau>''" and "has_type \<Sigma> (\<sigma> # \<Gamma>) b \<tau>''"
    by (auto elim: has_type_AbsE)
  with Abs.IH show ?case by simp
qed

lemma has_type_wf:
  assumes "sig_ok \<Sigma>" and "\<forall>\<tau>\<in>set \<Gamma>. wf_ty \<Sigma> \<tau>" and "has_type \<Sigma> \<Gamma> t \<tau>"
  shows "wf_ty \<Sigma> \<tau>"
  using assms(3,2)
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  then show ?case by simp
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by auto
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  then show ?case by simp
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  from App.IH(1) App.prems have "wf_ty \<Sigma> (funT \<sigma> \<tau>)" by simp
  then show ?case by (simp add: sig_ok_fun[OF assms(1)])
next
  case (Abs \<sigma> \<Gamma> b \<tau>)
  from Abs.hyps(1) Abs.prems have "wf_ty \<Sigma> \<tau>" by (intro Abs.IH) simp
  with Abs.hyps(1) show ?case by (simp add: sig_ok_fun[OF assms(1)])
qed

lemma has_type_weaken:
  assumes "has_type \<Sigma> \<Gamma> t \<rho>"
  shows "has_type \<Sigma> (\<Gamma> @ \<Delta>) t \<rho>"
  using assms
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  then show ?case by (simp add: has_type.Fv)
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by (simp add: has_type.Bv nth_append)
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  then show ?case by (simp add: has_type.Cst)
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  then show ?case by (simp add: has_type.App)
next
  case (Abs \<sigma> \<Gamma> b \<tau>)
  then show ?case by (simp add: has_type.Abs)
qed

subsection \<open>Preservation of typing by term operations\<close>

text \<open>
  Beta-instantiation.  Generalized over the shape @{term "\<Gamma>1 @ \<sigma> # \<Gamma>2"} of the context; the
  substituted term is closed, hence needs only weakening.
\<close>

lemma has_type_subst_bv_aux:
  assumes "has_type \<Sigma> \<Gamma> b \<rho>" and "\<Gamma> = \<Gamma>1 @ \<sigma> # \<Gamma>2" and "has_type \<Sigma> [] s \<sigma>"
  shows "has_type \<Sigma> (\<Gamma>1 @ \<Gamma>2) (subst_bv (length \<Gamma>1) s b) \<rho>"
  using assms(1,2)
proof (induction arbitrary: \<Gamma>1 rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  then show ?case by (simp add: has_type.Fv)
next
  case (Bv i \<Gamma> \<tau>)
  show ?case
  proof (cases "i < length \<Gamma>1")
    case True
    with Bv.hyps Bv.prems show ?thesis
      by (simp add: nth_append has_type.Bv)
  next
    case False
    show ?thesis
    proof (cases "i = length \<Gamma>1")
      case True
      with Bv.hyps Bv.prems have "\<tau> = \<sigma>" by simp
      with True has_type_weaken[OF assms(3), of "\<Gamma>1 @ \<Gamma>2"] show ?thesis by simp
    next
      case False
      with \<open>\<not> i < length \<Gamma>1\<close> obtain j where j: "i = length \<Gamma>1 + Suc j"
        by (metis add_Suc_right less_imp_Suc_add nat_neq_iff)
      with Bv.hyps Bv.prems show ?thesis
        by (simp add: nth_append has_type.Bv)
    qed
  qed
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  then show ?case by (simp add: has_type.Cst)
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  then show ?case by (simp add: has_type.App)
next
  case (Abs \<sigma>' \<Gamma> b \<tau>)
  from Abs.prems have "\<sigma>' # \<Gamma> = (\<sigma>' # \<Gamma>1) @ \<sigma> # \<Gamma>2" by simp
  from Abs.IH[OF this] Abs.hyps(1) show ?case by (simp add: has_type.Abs)
qed

lemma has_type_subst_bv:
  assumes "has_type \<Sigma> (\<Gamma>1 @ \<sigma> # \<Gamma>2) b \<rho>" and "has_type \<Sigma> [] s \<sigma>"
  shows "has_type \<Sigma> (\<Gamma>1 @ \<Gamma>2) (subst_bv (length \<Gamma>1) s b) \<rho>"
  using has_type_subst_bv_aux[OF assms(1) refl assms(2)] .

text \<open>
  Abstracting a free variable of well-formed type into the innermost new binder.
\<close>

lemma has_type_abs_fv:
  assumes "has_type \<Sigma> \<Gamma>1 t \<rho>" and "wf_ty \<Sigma> \<sigma>"
  shows "has_type \<Sigma> (\<Gamma>1 @ [\<sigma>]) (abs_fv (length \<Gamma>1) x \<sigma> t) \<rho>"
  using assms(1)
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x')
  show ?case
  proof (cases "x' = x \<and> \<tau> = \<sigma>")
    case True
    then show ?thesis by (simp add: has_type.Bv)
  next
    case False
    with Fv.hyps show ?thesis by (auto intro: has_type.Fv)
  qed
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by (simp add: has_type.Bv nth_append)
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  then show ?case by (simp add: has_type.Cst)
next
  case (App \<Gamma> f \<sigma>' \<tau> a)
  then show ?case by (simp add: has_type.App)
next
  case (Abs \<sigma>' \<Gamma> b \<tau>)
  then show ?case by (simp add: has_type.Abs)
qed

lemma has_type_inst_fv:
  assumes "has_type \<Sigma> \<Gamma> t \<rho>" and "\<And>x \<tau>. has_type \<Sigma> [] (\<sigma> x \<tau>) \<tau>"
  shows "has_type \<Sigma> \<Gamma> (inst_fv \<sigma> t) \<rho>"
  using assms(1)
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  from has_type_weaken[OF assms(2), of \<Gamma> x \<tau>] show ?case by simp
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by (simp add: has_type.Bv)
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  then show ?case by (simp add: has_type.Cst)
next
  case (App \<Gamma> f \<sigma>' \<tau> a)
  then show ?case by (simp add: has_type.App)
next
  case (Abs \<sigma>' \<Gamma> b \<tau>)
  then show ?case by (simp add: has_type.Abs)
qed

lemma has_type_tinst:
  assumes "has_type \<Sigma> \<Gamma> t \<rho>" and "\<And>a. wf_ty \<Sigma> (\<theta> a)"
  shows "has_type \<Sigma> (map (tsubst \<theta>) \<Gamma>) (tinst \<theta> t) (tsubst \<theta> \<rho>)"
  using assms(1)
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  from Fv.hyps wf_ty_tsubst[OF _ assms(2)] show ?case by (simp add: has_type.Fv)
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by (simp add: has_type.Bv)
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  from Cst.hyps(3) obtain \<theta>0 where "tsubst \<theta>0 \<sigma>0 = \<tau>" by blast
  then have eq: "tsubst \<theta> \<tau> = tsubst (\<lambda>a. tsubst \<theta> (\<theta>0 a)) \<sigma>0"
    by (subst tsubst_comp[symmetric]) simp
  have "has_type \<Sigma> (map (tsubst \<theta>) \<Gamma>) (Cst c (tsubst \<theta> \<tau>)) (tsubst \<theta> \<tau>)"
    by (rule has_type.Cst[OF Cst.hyps(1) wf_ty_tsubst[OF Cst.hyps(2) assms(2)]])
       (rule exI[of _ "\<lambda>a. tsubst \<theta> (\<theta>0 a)"], rule eq[symmetric])
  then show ?case by simp
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  then show ?case by (simp add: has_type.App)
next
  case (Abs \<sigma> \<Gamma> b \<tau>)
  from Abs.hyps(1) wf_ty_tsubst[OF _ assms(2)] Abs.IH show ?case
    by (simp add: has_type.Abs)
qed

subsection \<open>Typing of equations\<close>

text \<open>
  Typing of @{const mk_eq}: an equation is a Boolean whose two sides have the same type.
\<close>

lemma has_type_mk_eq_iff:
  assumes "sig_ok \<Sigma>"
  shows "has_type \<Sigma> \<Gamma> (mk_eq \<tau> s t) \<rho> \<longleftrightarrow>
    \<rho> = boolT \<and> wf_ty \<Sigma> \<tau> \<and> has_type \<Sigma> \<Gamma> s \<tau> \<and> has_type \<Sigma> \<Gamma> t \<tau>"
proof
  assume "has_type \<Sigma> \<Gamma> (mk_eq \<tau> s t) \<rho>"
  then obtain \<sigma>1 where t: "has_type \<Sigma> \<Gamma> t \<sigma>1"
    and fs: "has_type \<Sigma> \<Gamma> (App (Cst ''='' (funT \<tau> (funT \<tau> boolT))) s) (funT \<sigma>1 \<rho>)"
    unfolding mk_eq_def by (auto elim: has_type_AppE)
  from fs obtain \<sigma>2 where s: "has_type \<Sigma> \<Gamma> s \<sigma>2"
    and c: "has_type \<Sigma> \<Gamma> (Cst ''='' (funT \<tau> (funT \<tau> boolT))) (funT \<sigma>2 (funT \<sigma>1 \<rho>))"
    by (auto elim: has_type_AppE)
  from c have eq: "funT \<tau> (funT \<tau> boolT) = funT \<sigma>2 (funT \<sigma>1 \<rho>)"
    and wfT: "wf_ty \<Sigma> (funT \<tau> (funT \<tau> boolT))"
    by (auto elim: has_type_CstE)
  from eq have h: "\<tau> = \<sigma>2 \<and> \<tau> = \<sigma>1 \<and> boolT = \<rho>"
    by (auto simp only: ty.inject list.inject simp_thms)
  from wfT have "wf_ty \<Sigma> \<tau>" by simp
  with h s t show "\<rho> = boolT \<and> wf_ty \<Sigma> \<tau> \<and> has_type \<Sigma> \<Gamma> s \<tau> \<and> has_type \<Sigma> \<Gamma> t \<tau>"
    by auto
next
  assume "\<rho> = boolT \<and> wf_ty \<Sigma> \<tau> \<and> has_type \<Sigma> \<Gamma> s \<tau> \<and> has_type \<Sigma> \<Gamma> t \<tau>"
  then have \<rho>: "\<rho> = boolT" and wf\<tau>: "wf_ty \<Sigma> \<tau>"
    and s: "has_type \<Sigma> \<Gamma> s \<tau>" and t: "has_type \<Sigma> \<Gamma> t \<tau>" by simp_all
  have wfE: "wf_ty \<Sigma> (funT \<tau> (funT \<tau> boolT))"
    using wf\<tau> by (simp add: sig_ok_fun[OF assms] sig_ok_bool[OF assms])
  have "has_type \<Sigma> \<Gamma> (Cst ''='' (funT \<tau> (funT \<tau> boolT))) (funT \<tau> (funT \<tau> boolT))"
    using sig_ok_eq[OF assms] wfE by (auto intro!: has_type.Cst exI[of _ "\<lambda>_. \<tau>"])
  then have "has_type \<Sigma> \<Gamma> (App (Cst ''='' (funT \<tau> (funT \<tau> boolT))) s) (funT \<tau> boolT)"
    using s by (rule has_type.App)
  then have "has_type \<Sigma> \<Gamma> (mk_eq \<tau> s t) boolT"
    unfolding mk_eq_def using t by (rule has_type.App)
  with \<rho> show "has_type \<Sigma> \<Gamma> (mk_eq \<tau> s t) \<rho>" by simp
qed

end
