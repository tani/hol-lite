theory HOL_Lite_Derived
  imports HOL_Lite_Kernel
begin

section \<open>Derived rules and sanity checks\<close>

subsection \<open>Derived rules\<close>

text \<open>
  Derived rules double as end-to-end checks that the primitive rules compose as in HOL Light.
\<close>

context hol_lite
begin

lemma has_type_eq_const:
  assumes "wf_ty \<Sigma> \<tau>"
  shows "has_type \<Sigma> \<Gamma> (Cst ''='' (funT \<tau> (funT \<tau> boolT))) (funT \<tau> (funT \<tau> boolT))"
proof -
  have "wf_ty \<Sigma> (funT \<tau> (funT \<tau> boolT))"
    using assms by (simp add: sig_ok_fun[OF sig_ok] sig_ok_bool[OF sig_ok])
  with sig_ok_eq[OF sig_ok] show ?thesis
    by (auto intro!: has_type.Cst exI[of _ "\<lambda>_. \<tau>"])
qed

text \<open>Symmetry (HOL Light @{text SYM}).\<close>

lemma sym:
  assumes "derivable \<Gamma> (mk_eq \<tau> s t)"
  shows "derivable \<Gamma> (mk_eq \<tau> t s)"
proof -
  from derivable_typed[OF assms] have "has_type \<Sigma> [] (mk_eq \<tau> s t) boolT" by simp
  then have wf\<tau>: "wf_ty \<Sigma> \<tau>" and s: "has_type \<Sigma> [] s \<tau>"
    by (simp_all add: has_type_mk_eq_iff[OF sig_ok])
  have hE: "has_type \<Sigma> [] (Cst ''='' (funT \<tau> (funT \<tau> boolT))) (funT \<tau> (funT \<tau> boolT))"
    by (rule has_type_eq_const[OF wf\<tau>])
  have d1: "derivable {} (mk_eq (funT \<tau> (funT \<tau> boolT))
      (Cst ''='' (funT \<tau> (funT \<tau> boolT))) (Cst ''='' (funT \<tau> (funT \<tau> boolT))))"
    by (rule derivable.refl[OF hE])
  have d2: "derivable ({} \<union> \<Gamma>) (mk_eq (funT \<tau> boolT)
      (App (Cst ''='' (funT \<tau> (funT \<tau> boolT))) s) (App (Cst ''='' (funT \<tau> (funT \<tau> boolT))) t))"
    by (rule derivable.mk_comb[OF d1 assms])
  have d3: "derivable {} (mk_eq \<tau> s s)"
    by (rule derivable.refl[OF s])
  have d4: "derivable (({} \<union> \<Gamma>) \<union> {}) (mk_eq boolT (mk_eq \<tau> s s) (mk_eq \<tau> t s))"
    using derivable.mk_comb[OF d2 d3] by (simp add: mk_eq_def)
  from derivable.eq_mp[OF d4 d3] show ?thesis by simp
qed

text \<open>Congruence of application in the argument.\<close>

lemma ap_term:
  assumes "derivable \<Gamma> (mk_eq \<tau> x y)" and "has_type \<Sigma> [] f (funT \<tau> \<rho>)"
  shows "derivable \<Gamma> (mk_eq \<rho> (App f x) (App f y))"
proof -
  from derivable.mk_comb[OF derivable.refl[OF assms(2)] assms(1)]
  show ?thesis by simp
qed

text \<open>Congruence of application in the function.\<close>

lemma ap_thm:
  assumes "derivable \<Gamma> (mk_eq (funT \<sigma> \<rho>) f g)" and "has_type \<Sigma> [] a \<sigma>"
  shows "derivable \<Gamma> (mk_eq \<rho> (App f a) (App g a))"
proof -
  from derivable.mk_comb[OF assms(1) derivable.refl[OF assms(2)]]
  show ?thesis by simp
qed

end

subsection \<open>Non-vacuity and convention checks\<close>

text \<open>
  A concrete signature declaring only @{text fun}, @{text bool} and polymorphic equality.  The
  examples fail if @{const sig_ok} were unsatisfiable or if the index conventions of
  @{const abs_fv} and @{const subst_bv} were wrong.
\<close>

definition base_hsig :: hsig where
  "base_hsig = HSig (\<lambda>c. if c = ''fun'' then Some 2 else if c = ''bool'' then Some 0 else None)
                    (\<lambda>c. if c = ''='' then Some (funT (TyVar ''a'') (funT (TyVar ''a'') boolT))
                         else None)"

lemma sig_ok_base: "sig_ok base_hsig"
  by (auto simp: sig_ok_def base_hsig_def split: if_splits)

interpretation base: hol_lite base_hsig "{}"
  by unfold_locales (simp_all add: sig_ok_base)

lemma wf_ty_base_boolT: "wf_ty base_hsig boolT"
  by (simp add: base_hsig_def)

lemma base_refl_example:
  "base.derivable {} (mk_eq boolT (Fv ''p'' boolT) (Fv ''p'' boolT))"
  by (rule base.derivable.refl[OF has_type.Fv[OF wf_ty_base_boolT]])

lemma base_abs_example:
  "base.derivable {} (mk_eq (funT boolT boolT) (Abs boolT (Bv 0)) (Abs boolT (Bv 0)))"
proof -
  have "base.derivable {} (mk_eq boolT (Fv ''x'' boolT) (Fv ''x'' boolT))"
    by (rule base.derivable.refl[OF has_type.Fv[OF wf_ty_base_boolT]])
  from base.derivable.abs[OF this wf_ty_base_boolT, of "''x''"] show ?thesis by simp
qed

lemma base_beta_example:
  "base.derivable {} (mk_eq boolT (App (Abs boolT (Bv 0)) (Fv ''x'' boolT)) (Fv ''x'' boolT))"
proof -
  have "has_type base_hsig [] (Abs boolT (Bv 0)) (funT boolT boolT)"
    by (rule has_type.Abs[OF wf_ty_base_boolT has_type.Bv]) simp_all
  from base.derivable.beta[OF this, of "''x''"] show ?thesis by simp
qed

end
