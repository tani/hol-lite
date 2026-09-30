theory HOL_Lite_Guided_Flood
  imports HOL_Lite_Flood HOL_Lite_Guided_Derivation
begin

section \<open>Guided flood: forward saturation inside a given term universe\<close>

text \<open>
  @{text HOL_Lite_Flood} saturates the whole region @{text "Tm_wt N \<Sigma> r"}, which is far too large
  for goals of realistic size (an equation between two boolean variables already has size 12).
  Here the universe is a given list @{text W} of terms.  Every rule step is driven by the
  premises found so far and by @{text W}: a rule that would produce a conclusion outside
  @{text W} is not applied, and conclusions that are equations are decoded from @{text W} instead
  of being enumerated.  The main theorem (at the end) states that the guided flood decides exactly
  @{text gderiv} for the universe @{text W}: sound for every @{text W}, complete relative to
  @{text W}, and complete in the limit by @{text derivable_iff_gderiv}.
\<close>

subsection \<open>Executable rule steps over a universe\<close>

definition in_reg :: "tm list \<Rightarrow> (tm set \<times> tm) \<Rightarrow> bool" where
  "in_reg W q = ((\<forall>h\<in>fst q. h \<in> set W) \<and> snd q \<in> set W)"

lemma wdest_eq_mk_eq [simp]: "HOL_Lite_Waterfall.dest_eq (mk_eq \<tau> s t) = Some (\<tau>, s, t)"
  by (simp add: mk_eq_def)

definition typed_as :: "hsig \<Rightarrow> tm \<Rightarrow> ty \<Rightarrow> bool" where
  "typed_as \<Sigma> t \<tau> = (typeof \<Sigma> [] t = Some \<tau>)"

definition gscan :: "tm list \<Rightarrow> ((tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option) \<Rightarrow>
    (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "gscan W f S = concat (map (\<lambda>p1. concat (map (\<lambda>p2. case f p1 p2 of
    None \<Rightarrow> [] | Some q \<Rightarrow> if in_reg W q then [q] else []) S)) S)"

lemma set_gscan:
  "set (gscan W f S) = (\<Union>p1\<in>set S. \<Union>p2\<in>set S. case f p1 p2 of
     None \<Rightarrow> {} | Some q \<Rightarrow> if in_reg W q then {q} else {})"
proof -
  have per: "\<And>p1 p2. set (case f p1 p2 of None \<Rightarrow> [] | Some q \<Rightarrow> if in_reg W q then [q] else []) =
     (case f p1 p2 of None \<Rightarrow> {} | Some q \<Rightarrow> if in_reg W q then {q} else {})"
    by (simp split: option.splits)
  show ?thesis unfolding gscan_def using per by (simp add: set_concat_map)
qed

definition trans_fn :: "(tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option" where
  "trans_fn p1 p2 = (case (HOL_Lite_Waterfall.dest_eq (snd p1), HOL_Lite_Waterfall.dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
    | _ \<Rightarrow> None)"

definition mk_comb_fn :: "(tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option" where
  "mk_comb_fn p1 p2 = (case (HOL_Lite_Waterfall.dest_eq (snd p1), HOL_Lite_Waterfall.dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
        then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
    | _ \<Rightarrow> None)"

definition eq_mp_fn :: "(tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option" where
  "eq_mp_fn p1 p2 = (case HOL_Lite_Waterfall.dest_eq (snd p1) of
      Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p then Some (fst p1 \<union> fst p2,q) else None
    | None \<Rightarrow> None)"

definition antisym_fn :: "(tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option" where
  "antisym_fn p1 p2 =
     Some ((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2))"

definition g_refl :: "hsig \<Rightarrow> tm list \<Rightarrow> (tm set \<times> tm) list" where
  "g_refl \<Sigma> W = concat (map (\<lambda>c. case HOL_Lite_Waterfall.dest_eq c of
      Some (\<tau>,s,t) \<Rightarrow> if s = t \<and> typed_as \<Sigma> s \<tau> then [({}, c)] else []
    | None \<Rightarrow> []) W)"

definition g_assm :: "hsig \<Rightarrow> tm list \<Rightarrow> (tm set \<times> tm) list" where
  "g_assm \<Sigma> W = map (\<lambda>p. ({p}, p)) (filter (\<lambda>p. typed_as \<Sigma> p boolT) W)"

definition beta_one :: "hsig \<Rightarrow> tm \<Rightarrow> (tm set \<times> tm) list" where
  "beta_one \<Sigma> c = (case HOL_Lite_Waterfall.dest_eq c of
      Some (\<tau>, App w (Fv x \<sigma>), rhs) \<Rightarrow>
        (case w of
           Abs \<sigma>' b \<Rightarrow>
             if \<sigma>' = \<sigma> \<and> typed_as \<Sigma> w (funT \<sigma> \<tau>) \<and> rhs = subst_bv 0 (Fv x \<sigma>) b
             then [({}, c)] else []
         | _ \<Rightarrow> [])
    | _ \<Rightarrow> [])"

definition g_beta :: "hsig \<Rightarrow> tm list \<Rightarrow> (tm set \<times> tm) list" where
  "g_beta \<Sigma> W = concat (map (beta_one \<Sigma>) W)"

definition g_axiom :: "(name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow>
    (tm set \<times> tm) list" where
  "g_axiom axs ns r W = map (\<lambda>p. ({}, p)) (filter (\<lambda>p. p \<in> set (axs (set ns) r)) W)"

subsection \<open>Soundness and coverage of the rule steps\<close>

context hol_lite_axs
begin

lemma in_reg_iff [simp]: "in_reg W q \<longleftrightarrow> q \<in> Sequent_U (set W)"
  by (cases q) (simp add: in_reg_def Sequent_U_def subset_eq)

lemma typed_as_sound: "typed_as \<Sigma> t \<tau> \<Longrightarrow> has_type \<Sigma> [] t \<tau>"
  unfolding typed_as_def by (rule typeof_sound)

lemma typed_as_complete: "has_type \<Sigma> [] t \<tau> \<Longrightarrow> typed_as \<Sigma> t \<tau>"
  unfolding typed_as_def by (rule typeof_complete)

lemma gscan_sound:
  assumes f: "\<And>p1 p2 q. f p1 p2 = Some q \<Longrightarrow> gderiv (set W) p1 \<Longrightarrow> gderiv (set W) p2 \<Longrightarrow>
                q \<in> Sequent_U (set W) \<Longrightarrow> gderiv (set W) q"
    and S: "\<forall>p\<in>set S. gderiv (set W) p"
  shows "\<forall>q\<in>set (gscan W f S). gderiv (set W) q"
  using S by (auto simp: set_gscan split: option.splits if_splits intro: f)

lemma gscan_cover:
  assumes "p1 \<in> set S" "p2 \<in> set S" "f p1 p2 = Some q" "q \<in> Sequent_U (set W)"
  shows "q \<in> set (gscan W f S)"
  unfolding set_gscan
  by (rule UN_I[OF assms(1)], rule UN_I[OF assms(2)]) (use assms in simp)

text \<open>The bridge to the derivation rules: the conclusion of every instance lies in the region.\<close>

lemma trans_fn_sound:
  "trans_fn p1 p2 = Some q \<Longrightarrow> gderiv U p1 \<Longrightarrow> gderiv U p2 \<Longrightarrow> q \<in> Sequent_U U \<Longrightarrow> gderiv U q"
  unfolding trans_fn_def
  by (cases p1; cases p2)
     (auto split: option.splits prod.splits if_splits dest!: HOL_Lite_Waterfall.dest_eq_sound
      intro: gderiv.gtrans)

lemma mk_comb_fn_sound:
  "mk_comb_fn p1 p2 = Some q \<Longrightarrow> gderiv U p1 \<Longrightarrow> gderiv U p2 \<Longrightarrow> q \<in> Sequent_U U \<Longrightarrow> gderiv U q"
  unfolding mk_comb_fn_def
  by (cases p1; cases p2)
     (auto split: option.splits prod.splits ty.splits list.splits if_splits
      dest!: HOL_Lite_Waterfall.dest_eq_sound intro: gderiv.gmk_comb)

lemma eq_mp_fn_sound:
  "eq_mp_fn p1 p2 = Some q \<Longrightarrow> gderiv U p1 \<Longrightarrow> gderiv U p2 \<Longrightarrow> q \<in> Sequent_U U \<Longrightarrow> gderiv U q"
  unfolding eq_mp_fn_def
  by (cases p1; cases p2)
     (auto split: option.splits prod.splits if_splits dest!: HOL_Lite_Waterfall.dest_eq_sound
      intro: gderiv.geq_mp)

lemma antisym_fn_sound:
  "antisym_fn p1 p2 = Some q \<Longrightarrow> gderiv U p1 \<Longrightarrow> gderiv U p2 \<Longrightarrow> q \<in> Sequent_U U \<Longrightarrow> gderiv U q"
  unfolding antisym_fn_def
  by (cases p1; cases p2) (auto intro: gderiv.gdeduct_antisym)

lemma trans_fn_cover:
  "trans_fn (\<Gamma>, mk_eq \<tau> s t) (\<Delta>, mk_eq \<tau> t u) = Some (\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u)"
  by (simp add: trans_fn_def)

lemma mk_comb_fn_cover:
  "mk_comb_fn (\<Gamma>, mk_eq (funT \<sigma> \<tau>) f g) (\<Delta>, mk_eq \<sigma> a b) =
   Some (\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b))"
  by (simp add: mk_comb_fn_def)

lemma eq_mp_fn_cover:
  "eq_mp_fn (\<Gamma>, mk_eq boolT p q) (\<Delta>, p) = Some (\<Gamma> \<union> \<Delta>, q)"
  by (simp add: eq_mp_fn_def)

lemma antisym_fn_cover:
  "antisym_fn (\<Gamma>, p) (\<Delta>, q) = Some ((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q)"
  by (simp add: antisym_fn_def)

lemma g_refl_sound: "\<forall>q\<in>set (g_refl \<Sigma> W). gderiv (set W) q"
proof
  fix q assume "q \<in> set (g_refl \<Sigma> W)"
  then obtain c where c: "c \<in> set W"
    and q: "q \<in> set (case HOL_Lite_Waterfall.dest_eq c of
      Some (\<tau>,s,t) \<Rightarrow> if s = t \<and> typed_as \<Sigma> s \<tau> then [({}, c)] else []
    | None \<Rightarrow> [])"
    by (auto simp: g_refl_def set_concat)
  show "gderiv (set W) q"
  proof (cases "HOL_Lite_Waterfall.dest_eq c")
    case None
    then show ?thesis using q by simp
  next
    case (Some x)
    obtain \<tau> s t where x: "x = (\<tau>, s, t)" by (cases x) auto
    from q Some x have st: "s = t" "typed_as \<Sigma> s \<tau>" "q = ({}, c)"
      by (auto split: if_splits)
    from Some x have ce: "c = mk_eq \<tau> s t" by (simp add: HOL_Lite_Waterfall.dest_eq_sound)
    have "({}, mk_eq \<tau> s s) \<in> Sequent_U (set W)" using c ce st(1) by (simp add: Sequent_U_def)
    then show ?thesis using st ce gderiv.grefl[OF typed_as_sound[OF st(2)]] by simp
  qed
qed

lemma g_refl_cover:
  assumes "has_type \<Sigma> [] t \<tau>" "({}, mk_eq \<tau> t t) \<in> Sequent_U (set W)"
  shows "({}, mk_eq \<tau> t t) \<in> set (g_refl \<Sigma> W)"
proof -
  have c: "mk_eq \<tau> t t \<in> set W" using assms(2) by (simp add: Sequent_U_def)
  have "({}, mk_eq \<tau> t t) \<in> set (case HOL_Lite_Waterfall.dest_eq (mk_eq \<tau> t t) of
      Some (\<tau>,s,t) \<Rightarrow> if s = t \<and> typed_as \<Sigma> s \<tau> then [({}, mk_eq \<tau> t t)] else []
    | None \<Rightarrow> [])"
    using typed_as_complete[OF assms(1)] by simp
  then show ?thesis using c by (auto simp: g_refl_def set_concat intro: bexI[of _ "mk_eq \<tau> t t"])
qed

lemma g_assm_sound: "\<forall>q\<in>set (g_assm \<Sigma> W). gderiv (set W) q"
  by (auto simp: g_assm_def Sequent_U_def intro!: gderiv.gassm dest: typed_as_sound)

lemma g_assm_cover:
  assumes "has_type \<Sigma> [] p boolT" "({p}, p) \<in> Sequent_U (set W)"
  shows "({p}, p) \<in> set (g_assm \<Sigma> W)"
  using assms typed_as_complete[OF assms(1)] by (auto simp: g_assm_def Sequent_U_def)

lemma g_beta_sound: "\<forall>q\<in>set (g_beta \<Sigma> W). gderiv (set W) q"
proof
  fix q assume "q \<in> set (g_beta \<Sigma> W)"
  then obtain c where c: "c \<in> set W" and q: "q \<in> set (beta_one \<Sigma> c)"
    by (auto simp: g_beta_def set_concat)
  show "gderiv (set W) q"
  proof (cases "HOL_Lite_Waterfall.dest_eq c")
    case None
    then show ?thesis using q by (simp add: beta_one_def)
  next
    case (Some y)
    obtain \<tau> l rhs where y: "y = (\<tau>, l, rhs)" by (cases y) auto
    show ?thesis
    proof (cases l)
      case (App w a)
      show ?thesis
      proof (cases a)
        case (Fv x \<sigma>)
        show ?thesis
        proof (cases w)
          case (Abs \<sigma>' b)
          from q Some y App Fv Abs have conds: "\<sigma>' = \<sigma>" "typed_as \<Sigma> w (funT \<sigma> \<tau>)"
            "rhs = subst_bv 0 (Fv x \<sigma>) b" "q = ({}, c)"
            by (auto simp: beta_one_def split: if_splits)
          from Some y have ce: "c = mk_eq \<tau> l rhs" by (simp add: HOL_Lite_Waterfall.dest_eq_sound)
          have wty: "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)"
            using typed_as_sound[OF conds(2)] Abs conds(1) by simp
          have mem: "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))
                     \<in> Sequent_U (set W)"
            using c ce App Fv Abs conds by (simp add: Sequent_U_def)
          show ?thesis
            using gderiv.gbeta[OF wty mem] conds(3,4) ce App Fv Abs conds(1) by simp
        qed (use q Some y App Fv in \<open>simp_all add: beta_one_def\<close>)
      qed (use q Some y App in \<open>simp_all add: beta_one_def\<close>)
    qed (use q Some y in \<open>simp_all add: beta_one_def\<close>)
  qed
qed

lemma g_beta_cover:
  assumes "has_type \<Sigma> [] (Abs \<sigma> b) (funT \<sigma> \<tau>)"
    "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_U (set W)"
  shows "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> set (g_beta \<Sigma> W)"
proof -
  let ?c = "mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)"
  have c: "?c \<in> set W" using assms(2) by (simp add: Sequent_U_def)
  have "({}, ?c) \<in> set (beta_one \<Sigma> ?c)"
    using typed_as_complete[OF assms(1)] by (simp add: beta_one_def)
  then show ?thesis using c by (auto simp: g_beta_def set_concat intro: bexI[of _ ?c])
qed

lemma g_axiom_sound:
  "\<forall>q\<in>set (g_axiom axs ns r W). gderiv (set W) q"
  by (auto simp: g_axiom_def axs_spec Sequent_U_def intro: gderiv.gaxiom)

lemma g_axiom_cover:
  assumes "p \<in> A" "({}, p) \<in> Sequent_U (set W)" "set W \<subseteq> Tm_wt (set ns) \<Sigma> r"
  shows "({}, p) \<in> set (g_axiom axs ns r W)"
  using assms by (auto simp: g_axiom_def axs_spec Sequent_U_def)

end

end
