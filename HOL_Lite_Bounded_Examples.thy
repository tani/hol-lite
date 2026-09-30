theory HOL_Lite_Bounded_Examples
  imports HOL_Lite_Flood
begin

definition empty_axs :: "name set \<Rightarrow> nat \<Rightarrow> tm list" where
  "empty_axs N r = []"

interpretation search_base: hol_lite_axs base_hsig "{}" empty_axs
  by unfold_locales (simp_all add: sig_ok_base empty_axs_def)

lemma bounded_refl:
  "({}, mk_eq boolT (Fv ''p'' boolT) (Fv ''p'' boolT))
     \<in> search_base.sat_r {''fun'', ''bool'', ''='', ''p''} 20"
proof (rule search_base.bderiv_sat_r)
  show "finite {''fun'', ''bool'', ''='', ''p''}" by simp
  show "hol_lite.bderiv base_hsig {} {''fun'', ''bool'', ''='', ''p''} 20
    ({}, mk_eq boolT (Fv ''p'' boolT) (Fv ''p'' boolT))"
    apply (rule hol_lite.bderiv.brefl[OF base.hol_lite_axioms])
     apply (rule has_type.Fv[OF wf_ty_base_boolT])
    by (simp add: Sequent_r_def Tm_wt_def Tm_def Ty_def mk_eq_def base_hsig_def
      ty_inst_def)
qed

lemma bounded_refl_iteration:
  "({}, mk_eq boolT (Fv ''p'' boolT) (Fv ''p'' boolT))
    \<in> search_base.iterate_r {''fun'', ''bool'', ''='', ''p''} 20
        (card (Sequent_r {''fun'', ''bool'', ''='', ''p''} base_hsig 20))"
  using bounded_refl search_base.sat_r_finite_iteration[of "{''fun'', ''bool'', ''='', ''p''}" 20]
  by simp

lemma executable_assumption:
  "flood_decide base_hsig empty_axs [''bool'', ''p''] 2 ({Fv ''p'' boolT}, Fv ''p'' boolT)"
  by eval

lemma executable_non_theorem:
  "\<not> flood_decide base_hsig empty_axs [''bool'', ''p''] 2 ({}, Fv ''p'' boolT)"
  by eval

lemma executable_waterfall:
  "waterfall 1 [flood_processor base_hsig empty_axs [''bool'', ''p''] 2]
     ([Fv ''p'' boolT], Fv ''p'' boolT) = []"
  by eval

end
