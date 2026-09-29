theory HOL_Lite_Kernel
  imports HOL_Lite_Typing
begin

section \<open>The kernel\<close>

subsection \<open>Locale: signature and axioms\<close>

text \<open>
  The kernel is parametric in an acceptable signature @{term \<Sigma>} and a set of axioms @{term A}
  of Boolean type.  No definitional principles are provided: extension of the signature and
  axiom set is left to the user of the locale.
\<close>

locale hol_lite =
  fixes \<Sigma> :: hsig and A :: "tm set"
  assumes sig_ok: "sig_ok \<Sigma>"
    and axioms_typed: "\<And>p. p \<in> A \<Longrightarrow> has_type \<Sigma> [] p boolT"

context hol_lite
begin

subsection \<open>Derivable sequents\<close>

text \<open>
  @{term "derivable \<Gamma> c"} is the sequent @{text "\<Gamma> \<turnstile> c"}.  The rules are the ten primitive
  rules of HOL Light without the definitional principles, plus @{text axiom}.  Alpha-equivalence
  is equality thanks to de Bruijn indices.  The extra typing and well-formedness premises exist
  because @{typ ty} and @{typ tm} are unrestricted datatypes; HOL Light obtains them from its
  abstract types.  The side condition of @{text abs} says that @{term x} is not free in the
  hypotheses.
\<close>

inductive derivable :: "tm set \<Rightarrow> tm \<Rightarrow> bool" where
  refl:   "has_type \<Sigma> [] t \<tau> \<Longrightarrow> derivable {} (mk_eq \<tau> t t)"
| trans:  "derivable \<Gamma> (mk_eq \<tau> s t) \<Longrightarrow> derivable \<Delta> (mk_eq \<tau> t u)
            \<Longrightarrow> derivable (\<Gamma> \<union> \<Delta>) (mk_eq \<tau> s u)"
| mk_comb: "derivable \<Gamma> (mk_eq (funT \<sigma> \<tau>) f g) \<Longrightarrow> derivable \<Delta> (mk_eq \<sigma> a b)
            \<Longrightarrow> derivable (\<Gamma> \<union> \<Delta>) (mk_eq \<tau> (App f a) (App g b))"
| abs:    "derivable \<Gamma> (mk_eq \<tau> s t) \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<Longrightarrow> (\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p)
            \<Longrightarrow> derivable \<Gamma> (mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))"
| beta:   "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)
            \<Longrightarrow> derivable {} (mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))"
| "assume": "has_type \<Sigma> [] p boolT \<Longrightarrow> derivable {p} p"
| eq_mp:  "derivable \<Gamma> (mk_eq boolT p q) \<Longrightarrow> derivable \<Delta> p \<Longrightarrow> derivable (\<Gamma> \<union> \<Delta>) q"
| deduct_antisym: "derivable \<Gamma> p \<Longrightarrow> derivable \<Delta> q
            \<Longrightarrow> derivable ((\<Gamma> - {q}) \<union> (\<Delta> - {p})) (mk_eq boolT p q)"
| inst_type: "derivable \<Gamma> c \<Longrightarrow> (\<And>a. wf_ty \<Sigma> (\<theta> a)) \<Longrightarrow> derivable (tinst \<theta> ` \<Gamma>) (tinst \<theta> c)"
| inst:   "derivable \<Gamma> c \<Longrightarrow> (\<And>x \<tau>. has_type \<Sigma> [] (\<sigma> x \<tau>) \<tau>)
            \<Longrightarrow> derivable (inst_fv \<sigma> ` \<Gamma>) (inst_fv \<sigma> c)"
| axiom:  "p \<in> A \<Longrightarrow> derivable {} p"

subsection \<open>Derivable sequents are well-typed\<close>

text \<open>
  Main metatheorem: the conclusion and all hypotheses of a derivable sequent are closed terms
  of Boolean type.
\<close>

theorem derivable_typed:
  "derivable \<Gamma> c \<Longrightarrow> has_type \<Sigma> [] c boolT \<and> (\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT)"
proof (induction rule: derivable.induct)
  case (refl t \<tau>)
  from has_type_wf[OF sig_ok _ refl.hyps] have "wf_ty \<Sigma> \<tau>" by simp
  with refl.hyps show ?case by (simp add: has_type_mk_eq_iff[OF sig_ok])
next
  case (trans \<Gamma> \<tau> s t \<Delta> u)
  from trans.IH(1) trans.IH(2) show ?case
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
next
  case (mk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  from mk_comb.IH(1) have f: "has_type \<Sigma> [] f (funT \<sigma> \<tau>)" and g: "has_type \<Sigma> [] g (funT \<sigma> \<tau>)"
    and wfF: "wf_ty \<Sigma> (funT \<sigma> \<tau>)"
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
  from mk_comb.IH(2) have a: "has_type \<Sigma> [] a \<sigma>" and b: "has_type \<Sigma> [] b \<sigma>"
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
  from wfF have "wf_ty \<Sigma> \<tau>" by simp
  with f g a b mk_comb.IH show ?case
    by (auto simp: has_type_mk_eq_iff[OF sig_ok] intro: has_type.App)
next
  case (abs \<Gamma> \<tau> s t \<sigma> x)
  from abs.IH have wf\<tau>: "wf_ty \<Sigma> \<tau>" and s: "has_type \<Sigma> [] s \<tau>" and t: "has_type \<Sigma> [] t \<tau>"
    and hyps: "\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT"
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
  from has_type_abs_fv[OF s abs.hyps(2), of x] have "has_type \<Sigma> [\<sigma>] (abs_fv 0 x \<sigma> s) \<tau>" by simp
  with abs.hyps(2) have s': "has_type \<Sigma> [] (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (funT \<sigma> \<tau>)"
    by (rule has_type.Abs)
  from has_type_abs_fv[OF t abs.hyps(2), of x] have "has_type \<Sigma> [\<sigma>] (abs_fv 0 x \<sigma> t) \<tau>" by simp
  with abs.hyps(2) have t': "has_type \<Sigma> [] (Abs \<sigma> (abs_fv 0 x \<sigma> t)) (funT \<sigma> \<tau>)"
    by (rule has_type.Abs)
  from abs.hyps(2) wf\<tau> have "wf_ty \<Sigma> (funT \<sigma> \<tau>)" by (simp add: sig_ok_fun[OF sig_ok])
  with s' t' hyps show ?case by (simp add: has_type_mk_eq_iff[OF sig_ok])
next
  case (beta \<sigma> b \<tau> x)
  from beta.hyps obtain \<tau>' where \<tau>': "funT \<sigma> \<tau> = funT \<sigma> \<tau>'" and wf\<sigma>: "wf_ty \<Sigma> \<sigma>"
    and b: "has_type \<Sigma> [\<sigma>] b \<tau>'"
    by (auto elim: has_type_AbsE)
  from \<tau>' have \<tau>\<tau>': "\<tau>' = \<tau>" by simp
  from wf\<sigma> have x: "has_type \<Sigma> [] (Fv x \<sigma>) \<sigma>" by (rule has_type.Fv)
  from has_type_subst_bv[of \<Sigma> "[]" \<sigma> "[]" b \<tau>' "Fv x \<sigma>", OF _ x] b \<tau>\<tau>'
  have b': "has_type \<Sigma> [] (subst_bv 0 (Fv x \<sigma>) b) \<tau>" by simp
  from has_type.App[OF beta.hyps x] have app: "has_type \<Sigma> [] (App (Abs \<sigma> b) (Fv x \<sigma>)) \<tau>" .
  from has_type_wf[OF sig_ok _ app] have "wf_ty \<Sigma> \<tau>" by simp
  with app b' show ?case by (simp add: has_type_mk_eq_iff[OF sig_ok])
next
  case ("assume" p)
  then show ?case by simp
next
  case (eq_mp \<Gamma> p q \<Delta>)
  from eq_mp.IH(1) eq_mp.IH(2) show ?case
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
next
  case (deduct_antisym \<Gamma> p \<Delta> q)
  from deduct_antisym.IH have "has_type \<Sigma> [] p boolT" "has_type \<Sigma> [] q boolT"
    by simp_all
  with deduct_antisym.IH wf_boolT[OF sig_ok] show ?case
    by (auto simp: has_type_mk_eq_iff[OF sig_ok])
next
  case (inst_type \<Gamma> c \<theta>)
  from inst_type.IH have c: "has_type \<Sigma> [] c boolT"
    and hyps: "\<forall>p\<in>\<Gamma>. has_type \<Sigma> [] p boolT" by simp_all
  from has_type_tinst[OF c inst_type.hyps(2)] have c': "has_type \<Sigma> [] (tinst \<theta> c) boolT"
    by simp
  have "\<forall>q\<in>tinst \<theta> ` \<Gamma>. has_type \<Sigma> [] q boolT"
  proof
    fix q assume "q \<in> tinst \<theta> ` \<Gamma>"
    then obtain p where p: "p \<in> \<Gamma>" and q: "q = tinst \<theta> p" by blast
    from hyps p have "has_type \<Sigma> [] p boolT" by blast
    from has_type_tinst[OF this inst_type.hyps(2)] q show "has_type \<Sigma> [] q boolT" by simp
  qed
  with c' show ?case by simp
next
  case (inst \<Gamma> c \<sigma>)
  from inst.IH has_type_inst_fv[OF _ inst.hyps(2)] show ?case by auto
next
  case (axiom p)
  then show ?case by (simp add: axioms_typed)
qed

corollary derivable_closed [dest]: "derivable \<Gamma> c \<Longrightarrow> has_type \<Sigma> [] c boolT"
  by (rule conjunct1[OF derivable_typed])

end

end
