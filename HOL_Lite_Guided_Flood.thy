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

subsection \<open>Abstraction and type instantiation over a universe\<close>

text \<open>
  An abstraction conclusion is decoded from the universe: @{text dest_abs_eq} recognises
  @{text "mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> a) (Abs \<sigma> b)"}.  The bound name only has to range over the names in
  use and one fresh name: a name that occurs free in the equation must already be in use, and
  when it does not occur the result does not depend on it.

  For type instantiation the range of the substitution is the set of subtypes of the type
  annotations occurring in the universe: the conclusion contains @{text "\<theta> a"} inside an
  annotation whenever @{text a} occurs in the premise.
\<close>

definition dest_abs_eq :: "tm \<Rightarrow> (ty \<times> ty \<times> tm \<times> tm) option" where
  "dest_abs_eq c = (case HOL_Lite_Waterfall.dest_eq c of
      Some (TyApp fn [\<sigma>,\<tau>], Abs \<sigma>1 a, Abs \<sigma>2 b) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>1 = \<sigma> \<and> \<sigma>2 = \<sigma> then Some (\<sigma>, \<tau>, a, b) else None
    | _ \<Rightarrow> None)"

definition abs_one :: "name list \<Rightarrow> hsig \<Rightarrow> (tm set \<times> tm) \<Rightarrow> tm \<Rightarrow> (tm set \<times> tm) list" where
  "abs_one ns \<Sigma> p1 c = (case (HOL_Lite_Waterfall.dest_eq (snd p1), dest_abs_eq c) of
      (Some (\<tau>,s,t), Some (\<sigma>,\<tau>',a,b)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> wf_ty \<Sigma> \<sigma> \<and>
           (\<exists>x\<in>set (HOL_Lite_Waterfall.fresh_name ns # ns).
              (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> a = abs_fv 0 x \<sigma> s \<and> b = abs_fv 0 x \<sigma> t)
        then [(fst p1, c)] else []
    | _ \<Rightarrow> [])"

definition g_abs :: "hsig \<Rightarrow> name list \<Rightarrow> tm list \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "g_abs \<Sigma> ns W S = concat (map (\<lambda>p1. concat (map (abs_one ns \<Sigma> p1) W)) S)"

fun subtys :: "ty \<Rightarrow> ty list" where
  "subtys (TyVar a) = [TyVar a]"
| "subtys (TyApp c ts) = TyApp c ts # concat (map subtys ts)"

fun ann_tys :: "tm \<Rightarrow> ty list" where
  "ann_tys (Fv x \<tau>) = [\<tau>]"
| "ann_tys (Bv i) = []"
| "ann_tys (Cst c \<tau>) = [\<tau>]"
| "ann_tys (App f a) = ann_tys f @ ann_tys a"
| "ann_tys (Abs \<tau> b) = \<tau> # ann_tys b"

definition inst_tys :: "tm list \<Rightarrow> ty list" where
  "inst_tys W = remdups (concat (map (\<lambda>t. concat (map subtys (ann_tys t))) W))"

definition g_inst_vars :: "tm list \<Rightarrow> (tm set \<times> tm) \<Rightarrow> name list" where
  "g_inst_vars W p = remdups (tm_tyvar_list (snd p) @
    concat (map tm_tyvar_list (filter (\<lambda>t. t \<in> fst p) W)))"

definition g_inst :: "tm list \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "g_inst W S = concat (map (\<lambda>p1.
    concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))
      in if in_reg W q then [q] else [])
      (inst_envs (g_inst_vars W p1) (inst_tys W)))) S)"

lemma subtys_self: "\<tau> \<in> set (subtys \<tau>)"
  by (cases \<tau>) simp_all

lemma tsubst_in_subtys: "a \<in> ty_tyvars \<tau> \<Longrightarrow> \<theta> a \<in> set (subtys (tsubst \<theta> \<tau>))"
proof (induction \<tau> rule: ty.induct)
  case (TyVar b)
  then show ?case by (simp add: subtys_self)
next
  case (TyApp c ts)
  then obtain t where t: "t \<in> set ts" "a \<in> ty_tyvars t" by auto
  from TyApp.IH[OF t(1) t(2)] t(1) show ?case by (auto simp: image_iff)
qed

lemma ann_tys_tinst:
  "a \<in> tm_tyvars t \<Longrightarrow> \<exists>\<tau>\<in>set (ann_tys (tinst \<theta> t)). \<theta> a \<in> set (subtys \<tau>)"
  by (induction t rule: tm.induct) (auto dest: tsubst_in_subtys)

lemma inst_tys_mem:
  "u \<in> set W \<Longrightarrow> \<tau> \<in> set (ann_tys u) \<Longrightarrow> x \<in> set (subtys \<tau>) \<Longrightarrow> x \<in> set (inst_tys W)"
  unfolding inst_tys_def by (auto simp: set_concat image_iff intro!: bexI)

context hol_lite_axs
begin

lemma gderiv_region: "gderiv U p \<Longrightarrow> p \<in> Sequent_U U"
  by (induction rule: gderiv.induct) auto

lemma dest_abs_eq_sound:
  "dest_abs_eq c = Some (\<sigma>, \<tau>, a, b) \<Longrightarrow> c = mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> a) (Abs \<sigma> b)"
  unfolding dest_abs_eq_def
  by (auto split: option.splits prod.splits ty.splits list.splits tm.splits if_splits
      dest!: HOL_Lite_Waterfall.dest_eq_sound)

lemma dest_abs_eq_mk: "dest_abs_eq (mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> a) (Abs \<sigma> b)) = Some (\<sigma>, \<tau>, a, b)"
  by (simp add: dest_abs_eq_def)

lemma g_abs_sound:
  assumes S: "\<forall>p\<in>set S. gderiv (set W) p"
  shows "\<forall>q\<in>set (g_abs \<Sigma> ns W S). gderiv (set W) q"
proof
  fix q assume "q \<in> set (g_abs \<Sigma> ns W S)"
  then obtain p1 c where p1: "p1 \<in> set S" and c: "c \<in> set W" and q: "q \<in> set (abs_one ns \<Sigma> p1 c)"
    by (auto simp: g_abs_def set_concat)
  obtain G e where p1e: "p1 = (G, e)" by (cases p1) auto
  show "gderiv (set W) q"
  proof (cases "HOL_Lite_Waterfall.dest_eq e")
    case None
    then show ?thesis using q p1e by (simp add: abs_one_def)
  next
    case (Some y)
    obtain \<tau> s t where y: "y = (\<tau>, s, t)" by (cases y) auto
    show ?thesis
    proof (cases "dest_abs_eq c")
      case None
      then show ?thesis using q p1e Some y by (simp add: abs_one_def)
    next
      case (Some z)
      obtain \<sigma> \<tau>' a b where z: "z = (\<sigma>, \<tau>', a, b)" by (cases z) auto
      from q p1e \<open>HOL_Lite_Waterfall.dest_eq e = Some y\<close> y Some z obtain x where
        conds: "\<tau>' = \<tau>" "wf_ty \<Sigma> \<sigma>" "\<forall>p\<in>G. (x,\<sigma>) \<notin> fvs p"
          "a = abs_fv 0 x \<sigma> s" "b = abs_fv 0 x \<sigma> t" and qq: "q = (G, c)"
        by (auto simp: abs_one_def split: if_splits)
      have e: "e = mk_eq \<tau> s t" using HOL_Lite_Waterfall.dest_eq_sound \<open>HOL_Lite_Waterfall.dest_eq e = Some y\<close> y
        by blast
      have ce: "c = mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))"
        using dest_abs_eq_sound[OF \<open>dest_abs_eq c = Some z\<close>[unfolded z]] conds by simp
      have prem: "gderiv (set W) (G, mk_eq \<tau> s t)" using S p1 p1e e by auto
      have reg: "(G, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
                 \<in> Sequent_U (set W)"
        using gderiv_region[OF prem] c ce by (auto simp: Sequent_U_def)
      show ?thesis using gderiv.gabs[OF prem conds(2) conds(3) reg] qq ce by simp
    qed
  qed
qed


lemma fvs_mk_eq [simp]: "fvs (mk_eq \<tau> s t) = fvs s \<union> fvs t"
  by (simp add: mk_eq_def)

lemma fv_name_in_universe:
  assumes Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r" and u: "u \<in> set W" and fv: "(y, \<rho>) \<in> fvs u"
  shows "y \<in> set ns"
proof -
  from u Wt have "u \<in> Tm (set ns) \<Sigma> r" by (auto simp: Tm_wt_def)
  from Tm_fvs_name_mem[OF this fv] show ?thesis .
qed

lemma g_abs_cover:
  assumes p: "(\<Gamma>, mk_eq \<tau> s t) \<in> set S" and Ssub: "set S \<subseteq> Sequent_U (set W)"
    and Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r" and wf: "wf_ty \<Sigma> \<sigma>"
    and fresh: "\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p"
    and concl: "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
                \<in> Sequent_U (set W)"
  shows "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
         \<in> set (g_abs \<Sigma> ns W S)"
proof -
  let ?c = "mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))"
  have cW: "?c \<in> set W" using concl by (simp add: Sequent_U_def)
  have eW: "mk_eq \<tau> s t \<in> set W" using p Ssub by (auto simp: Sequent_U_def)
  have GW: "\<forall>g\<in>\<Gamma>. g \<in> set W" using p Ssub by (auto simp: Sequent_U_def)
  have names: "\<exists>x'\<in>set (HOL_Lite_Waterfall.fresh_name ns # ns).
      (\<forall>p\<in>\<Gamma>. (x', \<sigma>) \<notin> fvs p) \<and> abs_fv 0 x \<sigma> s = abs_fv 0 x' \<sigma> s \<and>
      abs_fv 0 x \<sigma> t = abs_fv 0 x' \<sigma> t"
  proof (cases "x \<in> set ns")
    case True
    then show ?thesis using fresh by (intro bexI[of _ x]) auto
  next
    case False
    have xs: "(x, \<sigma>) \<notin> fvs s" and xt: "(x, \<sigma>) \<notin> fvs t"
      using fv_name_in_universe[OF Wt eW, of x \<sigma>] False by auto
    have fr: "HOL_Lite_Waterfall.fresh_name ns \<notin> set ns" by (rule HOL_Lite_Waterfall.fresh_name_fresh)
    let ?x' = "HOL_Lite_Waterfall.fresh_name ns"
    have xs': "(?x', \<sigma>) \<notin> fvs s" and xt': "(?x', \<sigma>) \<notin> fvs t"
      using fv_name_in_universe[OF Wt eW, of ?x' \<sigma>] fr by auto
    have xg: "\<forall>p\<in>\<Gamma>. (?x', \<sigma>) \<notin> fvs p"
      using fv_name_in_universe[OF Wt] GW fr by blast
    show ?thesis
      using xg abs_fv_id[OF xs] abs_fv_id[OF xt] abs_fv_id[OF xs'] abs_fv_id[OF xt']
      by (intro bexI[of _ ?x']) auto
  qed
  then obtain x' where x': "x' \<in> set (HOL_Lite_Waterfall.fresh_name ns # ns)"
    "\<forall>p\<in>\<Gamma>. (x', \<sigma>) \<notin> fvs p" "abs_fv 0 x \<sigma> s = abs_fv 0 x' \<sigma> s"
    "abs_fv 0 x \<sigma> t = abs_fv 0 x' \<sigma> t" by blast
  have one: "abs_one ns \<Sigma> (\<Gamma>, mk_eq \<tau> s t) ?c = [(\<Gamma>, ?c)]"
    using wf x' by (auto simp: abs_one_def dest_abs_eq_mk intro!: bexI[of _ x'])
  show ?thesis
    unfolding g_abs_def set_concat_map
    by (rule UN_I[OF p], rule UN_I[OF cW]) (simp add: one)
qed

lemma subtys_wf: "wf_ty \<Sigma> \<tau> \<Longrightarrow> \<forall>u\<in>set (subtys \<tau>). wf_ty \<Sigma> u"
  by (induction \<tau> rule: ty.induct) (auto simp: ball_Un)

lemma ann_tys_wf: "wf_tm_ty \<Sigma> t \<Longrightarrow> \<forall>\<tau>\<in>set (ann_tys t). wf_ty \<Sigma> \<tau>"
  by (induction t rule: tm.induct) auto

lemma inst_tys_wf:
  assumes Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r"
  shows "\<forall>\<tau>\<in>set (inst_tys W). wf_ty \<Sigma> \<tau>"
proof
  fix \<tau> assume "\<tau> \<in> set (inst_tys W)"
  then obtain u a where u: "u \<in> set W" and a: "a \<in> set (ann_tys u)" and \<tau>: "\<tau> \<in> set (subtys a)"
    by (auto simp: inst_tys_def set_concat)
  from u Wt obtain \<rho> where "typeof \<Sigma> [] u = Some \<rho>" by (auto simp: Tm_wt_def)
  from has_type_wf_tm_ty[OF typeof_sound[OF this]] have "wf_tm_ty \<Sigma> u" .
  with ann_tys_wf a have "wf_ty \<Sigma> a" by blast
  with subtys_wf \<tau> show "wf_ty \<Sigma> \<tau>" by blast
qed

lemma set_g_inst_vars:
  "fst p \<subseteq> set W \<Longrightarrow> set (g_inst_vars W p) = inst_vars p"
  by (auto simp: g_inst_vars_def inst_vars_def subset_iff set_concat)

lemma map_of_map_pair: "a \<in> set vs \<Longrightarrow> map_of (map (\<lambda>x. (x, f x)) vs) a = Some (f a)"
  by (induction vs) auto

lemma g_inst_sound:
  assumes S: "\<forall>p\<in>set S. gderiv (set W) p" and Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r"
  shows "\<forall>q\<in>set (g_inst W S). gderiv (set W) q"
proof
  fix q assume "q \<in> set (g_inst W S)"
  then obtain p1 e where p1: "p1 \<in> set S"
    and e: "e \<in> set (inst_envs (g_inst_vars W p1) (inst_tys W))"
    and q: "q \<in> set (let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))
        in if in_reg W q then [q] else [])"
    by (auto simp: g_inst_def set_concat_map)
  define \<theta> where "\<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)"
  have qe: "q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))"
    and reg: "in_reg W (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))"
    using q by (auto simp: \<theta>_def Let_def split: if_splits)
  have ran: "set (map snd e) \<subseteq> set (inst_tys W)" using e by (simp add: set_inst_envs)
  have wf\<theta>: "\<And>a. wf_ty \<Sigma> (\<theta> a)"
  proof -
    fix a
    show "wf_ty \<Sigma> (\<theta> a)"
    proof (cases "map_of e a")
      case None
      then show ?thesis using wf_boolT[OF sig_ok] by (simp add: \<theta>_def)
    next
      case (Some t)
      from map_of_range[OF Some] have "t \<in> set (map snd e)" .
      then have "t \<in> set (inst_tys W)" by (rule rev_subsetD[OF _ ran])
      then show ?thesis using inst_tys_wf[OF Wt] Some by (simp add: \<theta>_def)
    qed
  qed
  obtain G c where p1e: "p1 = (G, c)" by (cases p1) auto
  from S p1 p1e have prem: "gderiv (set W) (G, c)" by auto
  from reg p1e have "(tinst \<theta> ` G, tinst \<theta> c) \<in> Sequent_U (set W)" by simp
  from gderiv.ginst_type[OF prem wf\<theta> this] show "gderiv (set W) q" using qe p1e by simp
qed

lemma g_inst_cover:
  assumes p: "(\<Gamma>, c) \<in> set S" and Ssub: "set S \<subseteq> Sequent_U (set W)"
    and concl: "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> Sequent_U (set W)"
  shows "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> set (g_inst W S)"
proof -
  have GW: "\<Gamma> \<subseteq> set W" using p Ssub by (auto simp: Sequent_U_def)
  let ?vars = "g_inst_vars W (\<Gamma>, c)"
  have V: "set ?vars = tm_tyvars c \<union> (\<Union>t\<in>\<Gamma>. tm_tyvars t)"
    using set_g_inst_vars[of "(\<Gamma>, c)" W] GW by (simp add: inst_vars_def)
  have cW': "tinst \<theta> c \<in> set W" using concl by (simp add: Sequent_U_def)
  have GW': "\<And>g. g \<in> \<Gamma> \<Longrightarrow> tinst \<theta> g \<in> set W" using concl by (auto simp: Sequent_U_def)
  have tyl: "\<And>a. a \<in> set ?vars \<Longrightarrow> \<theta> a \<in> set (inst_tys W)"
  proof -
    fix a assume a: "a \<in> set ?vars"
    from a V have "a \<in> tm_tyvars c \<or> (\<exists>g\<in>\<Gamma>. a \<in> tm_tyvars g)" by auto
    then show "\<theta> a \<in> set (inst_tys W)"
    proof
      assume "a \<in> tm_tyvars c"
      from ann_tys_tinst[OF this] obtain \<tau> where "\<tau> \<in> set (ann_tys (tinst \<theta> c))"
        "\<theta> a \<in> set (subtys \<tau>)" by blast
      with inst_tys_mem[OF cW'] show ?thesis by blast
    next
      assume "\<exists>g\<in>\<Gamma>. a \<in> tm_tyvars g"
      then obtain g where g: "g \<in> \<Gamma>" "a \<in> tm_tyvars g" by blast
      from ann_tys_tinst[OF g(2)] obtain \<tau> where "\<tau> \<in> set (ann_tys (tinst \<theta> g))"
        "\<theta> a \<in> set (subtys \<tau>)" by blast
      with inst_tys_mem[OF GW'[OF g(1)]] show ?thesis by blast
    qed
  qed
  let ?e = "map (\<lambda>a. (a, \<theta> a)) ?vars"
  have emem: "?e \<in> set (inst_envs ?vars (inst_tys W))"
    using tyl by (auto simp: set_inst_envs comp_def)
  define \<theta>' where "\<theta>' = (\<lambda>a. case map_of ?e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)"
  have agree: "\<And>a. a \<in> set ?vars \<Longrightarrow> \<theta>' a = \<theta> a"
    by (simp add: \<theta>'_def map_of_map_pair)
  have cc: "tinst \<theta>' c = tinst \<theta> c"
    by (rule tinst_cong) (use V agree in auto)
  have gg: "\<And>g. g \<in> \<Gamma> \<Longrightarrow> tinst \<theta>' g = tinst \<theta> g"
    by (rule tinst_cong) (use V agree in auto)
  have img: "tinst \<theta>' ` \<Gamma> = tinst \<theta> ` \<Gamma>" using gg by (auto simp: image_iff)
  show ?thesis
    unfolding g_inst_def set_concat_map
    by (rule UN_I[OF p], rule UN_I[OF emem]) (simp add: \<theta>'_def[symmetric] Let_def img cc concl)
qed

end

subsection \<open>The driver\<close>

definition g_step :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow>
    (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "g_step \<Sigma> axs ns r W S = remdups (
     g_refl \<Sigma> W @ g_assm \<Sigma> W @ g_beta \<Sigma> W @ g_axiom axs ns r W @
     gscan W trans_fn S @ gscan W mk_comb_fn S @ g_abs \<Sigma> ns W S @
     gscan W eq_mp_fn S @ gscan W antisym_fn S @ g_inst W S)"

fun g_rounds :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "g_rounds \<Sigma> axs ns r W 0 S = S"
| "g_rounds \<Sigma> axs ns r W (Suc k) S =
    (let T = remdups (S @ g_step \<Sigma> axs ns r W S)
     in if set T = set S then S else g_rounds \<Sigma> axs ns r W k T)"

text \<open>
  The universe actually used is the given list restricted to the terms that are well-typed and
  built from the names @{text ns} within size @{text r}; @{text "(ns, r)"} is only needed to
  query the axiom oracle, whose specification is stated for such terms.
\<close>

definition g_universe :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow> tm list" where
  "g_universe \<Sigma> ns r U = filter (tm_ok ns \<Sigma> r) (remdups U)"

definition g_bound :: "tm list \<Rightarrow> nat" where
  "g_bound W = 2 ^ length W * length W"

definition gflood_decide :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> tm list \<Rightarrow>
    (tm set \<times> tm) \<Rightarrow> bool" where
  "gflood_decide \<Sigma> axs ns r U p =
    (let W = g_universe \<Sigma> ns r U in p \<in> set (g_rounds \<Sigma> axs ns r W (g_bound W) []))"

context hol_lite_axs
begin

lemma set_g_universe: "set (g_universe \<Sigma> ns r U) = set U \<inter> Tm_wt (set ns) \<Sigma> r"
  by (auto simp: g_universe_def tm_ok_iff set_enum_tm)

lemma distinct_g_universe: "distinct (g_universe \<Sigma> ns r U)"
  by (simp add: g_universe_def)

lemma g_step_sound:
  assumes S: "\<forall>p\<in>set S. gderiv (set W) p" and Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r"
  shows "\<forall>q\<in>set (g_step \<Sigma> axs ns r W S). gderiv (set W) q"
proof -
  have a5: "\<forall>q\<in>set (gscan W trans_fn S). gderiv (set W) q"
    by (rule gscan_sound[OF _ S]) (use trans_fn_sound in blast)
  have a6: "\<forall>q\<in>set (gscan W mk_comb_fn S). gderiv (set W) q"
    by (rule gscan_sound[OF _ S]) (use mk_comb_fn_sound in blast)
  have a8: "\<forall>q\<in>set (gscan W eq_mp_fn S). gderiv (set W) q"
    by (rule gscan_sound[OF _ S]) (use eq_mp_fn_sound in blast)
  have a9: "\<forall>q\<in>set (gscan W antisym_fn S). gderiv (set W) q"
    by (rule gscan_sound[OF _ S]) (use antisym_fn_sound in blast)
  note a1 = g_refl_sound and a2 = g_assm_sound and a3 = g_beta_sound and a4 = g_axiom_sound
    and a7 = g_abs_sound[OF S] and a10 = g_inst_sound[OF S Wt]
  show ?thesis
    unfolding g_step_def set_remdups set_append
    using a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 by blast
qed

lemma g_rounds_sound:
  assumes Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r"
  shows "\<forall>p\<in>set S. gderiv (set W) p \<Longrightarrow>
         \<forall>p\<in>set (g_rounds \<Sigma> axs ns r W k S). gderiv (set W) p"
proof (induction k arbitrary: S)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?T = "remdups (S @ g_step \<Sigma> axs ns r W S)"
  have "\<forall>p\<in>set ?T. gderiv (set W) p"
    using Suc.prems g_step_sound[OF Suc.prems Wt] by auto
  then show ?case
    using Suc.IH[of ?T] Suc.prems by (auto simp: Let_def split: if_splits)
qed

lemma step_of_refl: "q \<in> set (g_refl \<Sigma> W) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_assm: "q \<in> set (g_assm \<Sigma> W) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_beta: "q \<in> set (g_beta \<Sigma> W) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_axiom: "q \<in> set (g_axiom axs ns r W) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_trans: "q \<in> set (gscan W trans_fn S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_mk_comb: "q \<in> set (gscan W mk_comb_fn S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_abs: "q \<in> set (g_abs \<Sigma> ns W S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_eq_mp: "q \<in> set (gscan W eq_mp_fn S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_antisym: "q \<in> set (gscan W antisym_fn S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)
lemma step_of_inst: "q \<in> set (g_inst W S) \<Longrightarrow> q \<in> set (g_step \<Sigma> axs ns r W S)"
  by (simp add: g_step_def)

text \<open>
  Completeness relative to the universe: a set of sequents inside the region that is closed under
  the executable step contains every derivation of @{text gderiv}.
\<close>

lemma closed_contains_gderiv:
  assumes Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r" and F: "set F \<subseteq> Sequent_U (set W)"
    and closed: "set (g_step \<Sigma> axs ns r W F) \<subseteq> set F"
  shows "gderiv (set W) p \<Longrightarrow> p \<in> set F"
proof (induction rule: gderiv.induct)
  case (grefl t \<tau>)
  have "({}, mk_eq \<tau> t t) \<in> set (g_refl \<Sigma> W)" by (rule g_refl_cover[OF grefl.hyps(1) grefl.hyps(2)])
  then have "({}, mk_eq \<tau> t t) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_refl)
  with closed show ?case by blast
next
  case (gtrans \<Gamma> \<tau> s t \<Delta> u)
  have "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> set (gscan W trans_fn F)"
    by (rule gscan_cover[where f = trans_fn, OF gtrans.IH(1) gtrans.IH(2) trans_fn_cover gtrans.hyps(3)])
  then have "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> s u) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_trans)
  with closed show ?case by blast
next
  case (gmk_comb \<Gamma> \<sigma> \<tau> f g \<Delta> a b)
  have "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> set (gscan W mk_comb_fn F)"
    by (rule gscan_cover[where f = mk_comb_fn, OF gmk_comb.IH(1) gmk_comb.IH(2) mk_comb_fn_cover gmk_comb.hyps(3)])
  then have "(\<Gamma> \<union> \<Delta>, mk_eq \<tau> (App f a) (App g b)) \<in> set (g_step \<Sigma> axs ns r W F)"
    by (rule step_of_mk_comb)
  with closed show ?case by blast
next
  case (gabs \<Gamma> \<tau> s t \<sigma> x)
  have "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
        \<in> set (g_abs \<Sigma> ns W F)"
    by (rule g_abs_cover[OF gabs.IH F Wt gabs.hyps(2) gabs.hyps(3) gabs.hyps(4)])
  then have "(\<Gamma>, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t)))
        \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_abs)
  with closed show ?case by blast
next
  case (gbeta \<sigma> b \<tau> x)
  have "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> set (g_beta \<Sigma> W)"
    by (rule g_beta_cover[OF gbeta.hyps(1) gbeta.hyps(2)])
  then have "({}, mk_eq \<tau> (App (Abs \<sigma> b) (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))
      \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_beta)
  with closed show ?case by blast
next
  case (gassm p)
  have "({p}, p) \<in> set (g_assm \<Sigma> W)" by (rule g_assm_cover[OF gassm.hyps(1) gassm.hyps(2)])
  then have "({p}, p) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_assm)
  with closed show ?case by blast
next
  case (geq_mp \<Gamma> p q \<Delta>)
  have "(\<Gamma> \<union> \<Delta>, q) \<in> set (gscan W eq_mp_fn F)"
    by (rule gscan_cover[where f = eq_mp_fn, OF geq_mp.IH(1) geq_mp.IH(2) eq_mp_fn_cover geq_mp.hyps(3)])
  then have "(\<Gamma> \<union> \<Delta>, q) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_eq_mp)
  with closed show ?case by blast
next
  case (gdeduct_antisym \<Gamma> p \<Delta> q)
  have "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> set (gscan W antisym_fn F)"
    by (rule gscan_cover[where f = antisym_fn, OF gdeduct_antisym.IH(1) gdeduct_antisym.IH(2) antisym_fn_cover
        gdeduct_antisym.hyps(3)])
  then have "((\<Gamma> - {q}) \<union> (\<Delta> - {p}), mk_eq boolT p q) \<in> set (g_step \<Sigma> axs ns r W F)"
    by (rule step_of_antisym)
  with closed show ?case by blast
next
  case (ginst_type \<Gamma> c \<theta>)
  have "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> set (g_inst W F)"
    by (rule g_inst_cover[OF ginst_type.IH F ginst_type.hyps(3)])
  then have "(tinst \<theta> ` \<Gamma>, tinst \<theta> c) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_inst)
  with closed show ?case by blast
next
  case (gaxiom p)
  have "({}, p) \<in> set (g_axiom axs ns r W)"
    by (rule g_axiom_cover[OF gaxiom.hyps(1) gaxiom.hyps(2) Wt])
  then have "({}, p) \<in> set (g_step \<Sigma> axs ns r W F)" by (rule step_of_axiom)
  with closed show ?case by blast
qed

end

end
