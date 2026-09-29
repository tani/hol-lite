theory HOL_Lite_Waterfall
  imports HOL_Lite_Check HOL_Lite_Derived HOL_Lite_L8
begin

section \<open>A Boyer-Moore-style waterfall\<close>

text \<open>
  This theory builds an ACL2/Boyer-Moore-style proof-search driver on top of the executable
  type checker of HOL_Lite_Check.  A @{text processor} inspects a @{text goal} (a
  list of hypotheses and a conclusion) and either makes no progress (@{text Unchanged}), closes
  it outright (@{text Closed}), or reduces it to a list of new subgoals (@{text Subgoals}).
  @{text waterfall} repeatedly re-runs the processor list from the top on every residual
  subgoal, Boyer-Moore style, up to a fuel bound @{text n} (termination is not guaranteed in
  general, hence the bound), and returns the list of goals it could not close.  All functions
  are defined at top level, with the signature @{text \<Sigma>} as an explicit argument, so they stay
  executable by @{command value} or the @{text eval} proof method; only the soundness theorems live inside the
  @{locale hol_lite} context, since they refer to @{text derivable}.
\<close>

subsection \<open>Goals, outcomes, processors\<close>

type_synonym goal = "tm list \<times> tm"

datatype outcome = Unchanged | Closed | Subgoals "goal list"

type_synonym processor = "goal \<Rightarrow> outcome"

subsection \<open>Destructing an equation\<close>

fun dest_eq :: "tm \<Rightarrow> (ty \<times> tm \<times> tm) option" where
  "dest_eq (App (App (Cst eq (TyApp fn [\<tau>, TyApp fn2 [\<tau>2, \<rho>2]])) s) t) =
     (if eq = ''='' \<and> fn = ''fun'' \<and> fn2 = ''fun'' \<and> \<tau> = \<tau>2 \<and> \<rho>2 = boolT
      then Some (\<tau>, s, t) else None)"
| "dest_eq _ = None"

lemma dest_eq_sound:
  assumes "dest_eq c = Some (\<tau>, s, t)"
  shows "c = mk_eq \<tau> s t"
  using assms
  by (induction c rule: dest_eq.induct) (auto simp: mk_eq_def split: if_splits)

subsection \<open>Closedness at a binder depth\<close>

fun closed_at :: "nat \<Rightarrow> tm \<Rightarrow> bool" where
  "closed_at k (Fv x \<tau>) = True"
| "closed_at k (Bv i) = (i < k)"
| "closed_at k (Cst c \<tau>) = True"
| "closed_at k (App f a) = (closed_at k f \<and> closed_at k a)"
| "closed_at k (Abs \<tau> b) = closed_at (Suc k) b"

subsection \<open>Fresh names\<close>

fun fvs_list :: "tm \<Rightarrow> name list" where
  "fvs_list (Fv x \<tau>) = [x]"
| "fvs_list (Bv i) = []"
| "fvs_list (Cst c \<tau>) = []"
| "fvs_list (App f a) = fvs_list f @ fvs_list a"
| "fvs_list (Abs \<tau> b) = fvs_list b"

lemma fvs_list_sound: "(x, \<tau>) \<in> fvs t \<Longrightarrow> x \<in> set (fvs_list t)"
  by (induction t) auto

definition fv_names :: "tm list \<Rightarrow> name list" where
  "fv_names ts = concat (map fvs_list ts)"

lemma fv_names_sound: "p \<in> set ts \<Longrightarrow> (x, \<tau>) \<in> fvs p \<Longrightarrow> x \<in> set (fv_names ts)"
  using fvs_list_sound[of x \<tau> p] by (auto simp: fv_names_def)

definition fresh_name :: "name list \<Rightarrow> name" where
  "fresh_name ns = replicate (Suc (foldr (\<lambda>n acc. max (length n) acc) ns 0)) (CHR ''x'')"

lemma fresh_name_length: "length (fresh_name ns) = Suc (foldr (\<lambda>n acc. max (length n) acc) ns 0)"
  by (simp add: fresh_name_def)

lemma length_le_foldr_max: "n \<in> set ns \<Longrightarrow> length n \<le> foldr (\<lambda>n acc. max (length n) acc) ns 0"
  by (induction ns) auto

lemma fresh_name_fresh: "fresh_name ns \<notin> set ns"
proof
  assume mem: "fresh_name ns \<in> set ns"
  from length_le_foldr_max[OF mem] have "length (fresh_name ns) \<le> foldr (\<lambda>n acc. max (length n) acc) ns 0" .
  with fresh_name_length show False by simp
qed

lemma fresh_name_not_free:
  assumes "p \<in> set ts"
  shows "(fresh_name (fv_names ts), \<tau>) \<notin> fvs p"
proof
  assume "(fresh_name (fv_names ts), \<tau>) \<in> fvs p"
  from fv_names_sound[OF assms this] have "fresh_name (fv_names ts) \<in> set (fv_names ts)" .
  with fresh_name_fresh show False by simp
qed

subsection \<open>Undoing @{const subst_bv} by @{const abs_fv}\<close>

lemma abs_fv_subst_bv_id:
  assumes "closed_at (Suc k) t" and "(x, \<sigma>) \<notin> fvs t"
  shows "abs_fv k x \<sigma> (subst_bv k (Fv x \<sigma>) t) = t"
  using assms
proof (induction t arbitrary: k)
  case (Fv y \<tau>)
  then show ?case by auto
next
  case (Bv i)
  then show ?case by auto
next
  case (Cst c \<tau>)
  then show ?case by simp
next
  case (App f a)
  then show ?case by simp
next
  case (Abs \<tau> b)
  then show ?case by simp
qed

subsection \<open>Driver\<close>

fun run_procs :: "processor list \<Rightarrow> goal \<Rightarrow> outcome" where
  "run_procs [] g = Unchanged"
| "run_procs (p # ps) g = (if p g = Unchanged then run_procs ps g else p g)"

fun waterfall :: "nat \<Rightarrow> processor list \<Rightarrow> goal \<Rightarrow> goal list" where
  "waterfall 0 ps g = [g]"
| "waterfall (Suc n) ps g = (case run_procs ps g of
      Unchanged \<Rightarrow> [g]
    | Closed \<Rightarrow> []
    | Subgoals gs \<Rightarrow> concat (map (waterfall n ps) gs))"

subsection \<open>Closers and decomposers\<close>

fun p_refl :: "hsig \<Rightarrow> processor" where
  "p_refl \<Sigma> (H, c) = (case dest_eq c of
      None \<Rightarrow> Unchanged
    | Some (\<tau>, s, t) \<Rightarrow> if s = t \<and> typeof \<Sigma> [] s = Some \<tau> then Closed else Unchanged)"

fun p_assume :: "hsig \<Rightarrow> processor" where
  "p_assume \<Sigma> (H, c) = (if c \<in> set H \<and> typeof \<Sigma> [] c = Some boolT then Closed else Unchanged)"

fun p_assume_sym :: "hsig \<Rightarrow> processor" where
  "p_assume_sym \<Sigma> (H, c) = (case dest_eq c of
      None \<Rightarrow> Unchanged
    | Some (\<tau>, s, t) \<Rightarrow>
        if mk_eq \<tau> t s \<in> set H \<and> typeof \<Sigma> [] (mk_eq \<tau> t s) = Some boolT
        then Closed else Unchanged)"

fun p_cong :: "hsig \<Rightarrow> processor" where
  "p_cong \<Sigma> (H, c) = (case dest_eq c of
      None \<Rightarrow> Unchanged
    | Some (\<tau>, l, r) \<Rightarrow>
       (case l of
          App f a \<Rightarrow> (case r of
             App g b \<Rightarrow> (case typeof \<Sigma> [] a of
                            None \<Rightarrow> Unchanged
                          | Some \<sigma> \<Rightarrow> Subgoals [(H, mk_eq (funT \<sigma> \<tau>) f g), (H, mk_eq \<sigma> a b)])
           | _ \<Rightarrow> Unchanged)
        | _ \<Rightarrow> Unchanged))"

fun p_abs :: "hsig \<Rightarrow> processor" where
  "p_abs \<Sigma> (H, c) = (case dest_eq c of
      None \<Rightarrow> Unchanged
    | Some (\<tau>0, l, r) \<Rightarrow>
       (case l of
          Abs \<sigma> s \<Rightarrow> (case r of
             Abs \<sigma>' t \<Rightarrow>
               (case \<tau>0 of
                  TyApp fn [\<sigma>2, \<tau>] \<Rightarrow>
                    if fn = ''fun'' \<and> \<sigma>2 = \<sigma> \<and> \<sigma> = \<sigma>' \<and> wf_ty \<Sigma> \<sigma>
                       \<and> closed_at (Suc 0) s \<and> closed_at (Suc 0) t
                    then
                      Subgoals [(H, mk_eq \<tau> (subst_bv 0 (Fv (fresh_name (fv_names (c # H))) \<sigma>) s)
                                              (subst_bv 0 (Fv (fresh_name (fv_names (c # H))) \<sigma>) t))]
                    else Unchanged
                | _ \<Rightarrow> Unchanged)
           | _ \<Rightarrow> Unchanged)
        | _ \<Rightarrow> Unchanged))"

definition default_procs :: "hsig \<Rightarrow> processor list" where
  "default_procs \<Sigma> = [p_refl \<Sigma>, p_assume \<Sigma>, p_assume_sym \<Sigma>, p_cong \<Sigma>, p_abs \<Sigma>]"

subsection \<open>Soundness\<close>

context hol_lite
begin

fun provable :: "goal \<Rightarrow> bool" where
  "provable (H, c) = (\<exists>\<Gamma>. \<Gamma> \<subseteq> set H \<and> derivable \<Gamma> c)"

lemma provable_iff: "provable g = (\<exists>\<Gamma>. \<Gamma> \<subseteq> set (fst g) \<and> derivable \<Gamma> (snd g))"
  by (cases g) simp

definition sound_proc :: "processor \<Rightarrow> bool" where
  "sound_proc p \<longleftrightarrow>
     (\<forall>g. (p g = Closed \<longrightarrow> provable g) \<and>
          (\<forall>gs. p g = Subgoals gs \<longrightarrow> (\<forall>g'\<in>set gs. provable g') \<longrightarrow> provable g))"

lemma run_procs_sound:
  assumes "\<forall>p\<in>set ps. sound_proc p"
  shows "(run_procs ps g = Closed \<longrightarrow> provable g) \<and>
         (\<forall>gs. run_procs ps g = Subgoals gs \<longrightarrow> (\<forall>g'\<in>set gs. provable g') \<longrightarrow> provable g)"
  using assms
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "p g = Unchanged")
    case True
    then have "run_procs (p # ps) g = run_procs ps g" by simp
    moreover from Cons.prems have "\<forall>q\<in>set ps. sound_proc q" by simp
    ultimately show ?thesis using Cons.IH by simp
  next
    case False
    then have eq: "run_procs (p # ps) g = p g" by simp
    from Cons.prems have sp: "sound_proc p" by simp
    from sp[unfolded sound_proc_def] have "(p g = Closed \<longrightarrow> provable g) \<and>
        (\<forall>gs. p g = Subgoals gs \<longrightarrow> (\<forall>g'\<in>set gs. provable g') \<longrightarrow> provable g)" by blast
    with eq show ?thesis by simp
  qed
qed

lemma waterfall_sound:
  assumes procs: "\<forall>p\<in>set ps. sound_proc p"
    and residual: "\<forall>g'\<in>set (waterfall n ps g). provable g'"
  shows "provable g"
  using residual
proof (induction n arbitrary: g)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "run_procs ps g")
    case Unchanged
    with Suc.prems show ?thesis by simp
  next
    case Closed
    from run_procs_sound[OF procs] Closed show ?thesis by simp
  next
    case (Subgoals gs)
    have "\<forall>g'\<in>set gs. provable g'"
    proof
      fix g' assume mem: "g' \<in> set gs"
      have "set (waterfall (Suc n) ps g) = (\<Union>h\<in>set gs. set (waterfall n ps h))"
        using Subgoals by simp
      with mem have "set (waterfall n ps g') \<subseteq> set (waterfall (Suc n) ps g)" by auto
      with Suc.prems have "\<forall>h\<in>set (waterfall n ps g'). provable h" by auto
      then show "provable g'" by (rule Suc.IH)
    qed
    with run_procs_sound[OF procs] Subgoals show ?thesis by simp
  qed
qed

corollary waterfall_prove:
  assumes "\<forall>p\<in>set ps. sound_proc p" and "waterfall n ps ([], c) = []"
  shows "derivable {} c"
proof -
  from assms(2) have "\<forall>g'\<in>set (waterfall n ps ([], c)). provable g'" by simp
  with waterfall_sound[OF assms(1)] have "provable ([], c)" by blast
  then obtain \<Gamma> where "\<Gamma> \<subseteq> set []" and "derivable \<Gamma> c" by auto
  then show ?thesis by simp
qed

lemma p_refl_not_Subgoals: "p_refl \<Sigma> gl \<noteq> Subgoals gs"
proof (cases gl)
  case (Pair H c)
  then show ?thesis by (simp add: p_refl.simps split: option.splits if_splits)
qed

lemma sound_p_refl: "sound_proc (p_refl \<Sigma>)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix gl
  assume peq: "p_refl \<Sigma> gl = Closed"
  obtain H c where gl_def: "gl = (H, c)" by (cases gl)
  from peq[unfolded gl_def] obtain \<tau> s where
      de: "HOL_Lite_Waterfall.dest_eq c = Some (\<tau>, s, s)" and ty: "typeof \<Sigma> [] s = Some \<tau>"
    by (auto simp: p_refl.simps split: option.splits if_splits)
  from HOL_Lite_Waterfall.dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> s s" .
  from typeof_sound[OF ty] have "has_type \<Sigma> [] s \<tau>" .
  from derivable.refl[OF this] have "derivable {} (mk_eq \<tau> s s)" .
  with c_eq gl_def show "provable gl" by (auto simp: provable.simps)
next
  fix gl gs
  assume peq: "p_refl \<Sigma> gl = Subgoals gs" and "\<forall>g'\<in>set gs. provable g'"
  with p_refl_not_Subgoals show "provable gl" by blast
qed

lemma p_assume_not_Subgoals: "p_assume \<Sigma> gl \<noteq> Subgoals gs"
proof (cases gl)
  case (Pair H c)
  then show ?thesis by (simp add: p_assume.simps)
qed

lemma sound_p_assume: "sound_proc (p_assume \<Sigma>)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix gl
  assume peq: "p_assume \<Sigma> gl = Closed"
  obtain H c where gl_def: "gl = (H, c)" by (cases gl)
  from peq[unfolded gl_def] have mem: "c \<in> set H" and ty: "typeof \<Sigma> [] c = Some boolT"
    by (auto simp: p_assume.simps split: if_splits)
  from typeof_sound[OF ty] have "has_type \<Sigma> [] c boolT" .
  from derivable.assm[OF this] have "derivable {c} c" .
  with mem gl_def show "provable gl" by (auto simp: provable.simps)
next
  fix gl gs
  assume peq: "p_assume \<Sigma> gl = Subgoals gs" and "\<forall>g'\<in>set gs. provable g'"
  with p_assume_not_Subgoals show "provable gl" by blast
qed

lemma p_assume_sym_not_Subgoals: "p_assume_sym \<Sigma> gl \<noteq> Subgoals gs"
proof (cases gl)
  case (Pair H c)
  then show ?thesis by (simp add: p_assume_sym.simps split: option.splits if_splits)
qed

lemma sound_p_assume_sym: "sound_proc (p_assume_sym \<Sigma>)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix gl
  assume peq: "p_assume_sym \<Sigma> gl = Closed"
  obtain H c where gl_def: "gl = (H, c)" by (cases gl)
  from peq[unfolded gl_def] obtain \<tau> s t where
      de: "HOL_Lite_Waterfall.dest_eq c = Some (\<tau>, s, t)"
      and mem: "mk_eq \<tau> t s \<in> set H" and ty: "typeof \<Sigma> [] (mk_eq \<tau> t s) = Some boolT"
    by (auto simp: p_assume_sym.simps split: option.splits if_splits)
  from HOL_Lite_Waterfall.dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> s t" .
  from typeof_sound[OF ty] have "has_type \<Sigma> [] (mk_eq \<tau> t s) boolT" .
  from derivable.assm[OF this] have "derivable {mk_eq \<tau> t s} (mk_eq \<tau> t s)" .
  from sym[OF this] have "derivable {mk_eq \<tau> t s} (mk_eq \<tau> s t)" .
  with c_eq mem gl_def show "provable gl" by (auto simp: provable.simps)
next
  fix gl gs
  assume peq: "p_assume_sym \<Sigma> gl = Subgoals gs" and "\<forall>g'\<in>set gs. provable g'"
  with p_assume_sym_not_Subgoals show "provable gl" by blast
qed

lemma p_cong_not_Closed: "p_cong \<Sigma> gl \<noteq> Closed"
proof (cases gl)
  case (Pair H c)
  then show ?thesis by (simp add: p_cong.simps split: option.splits tm.splits)
qed

lemma p_cong_SubgoalsE:
  assumes "p_cong \<Sigma> (H, c) = Subgoals gs"
  obtains \<tau> f a g b \<sigma> where "HOL_Lite_Waterfall.dest_eq c = Some (\<tau>, App f a, App g b)"
    and "typeof \<Sigma> [] a = Some \<sigma>"
    and "gs = [(H, mk_eq (funT \<sigma> \<tau>) f g), (H, mk_eq \<sigma> a b)]"
  using assms
  by (auto simp: p_cong.simps split: option.splits tm.splits)

lemma sound_p_cong: "sound_proc (p_cong \<Sigma>)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix gl
  assume "p_cong \<Sigma> gl = Closed"
  with p_cong_not_Closed show "provable gl" by simp
next
  fix gl gs
  assume peq: "p_cong \<Sigma> gl = Subgoals gs" and prov: "\<forall>g'\<in>set gs. provable g'"
  obtain H c where gl_def: "gl = (H, c)" by (cases gl)
  from peq[unfolded gl_def] obtain \<tau> f a g b \<sigma> where
      de: "HOL_Lite_Waterfall.dest_eq c = Some (\<tau>, App f a, App g b)"
      and ty: "typeof \<Sigma> [] a = Some \<sigma>"
      and gs_def: "gs = [(H, mk_eq (funT \<sigma> \<tau>) f g), (H, mk_eq \<sigma> a b)]"
    by (rule p_cong_SubgoalsE)
  from HOL_Lite_Waterfall.dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> (App f a) (App g b)" .
  from prov gs_def have prov1: "provable (H, mk_eq (funT \<sigma> \<tau>) f g)"
    and prov2: "provable (H, mk_eq \<sigma> a b)" by simp_all
  from prov1[unfolded provable.simps] obtain \<Gamma>1 where \<Gamma>1: "\<Gamma>1 \<subseteq> set H"
    and d1: "derivable \<Gamma>1 (mk_eq (funT \<sigma> \<tau>) f g)" by blast
  from prov2[unfolded provable.simps] obtain \<Gamma>2 where \<Gamma>2: "\<Gamma>2 \<subseteq> set H"
    and d2: "derivable \<Gamma>2 (mk_eq \<sigma> a b)" by blast
  from derivable.mk_comb[OF d1 d2] have d: "derivable (\<Gamma>1 \<union> \<Gamma>2) (mk_eq \<tau> (App f a) (App g b))" .
  have "provable (H, mk_eq \<tau> (App f a) (App g b))"
    unfolding provable.simps by (rule exI[where x="\<Gamma>1 \<union> \<Gamma>2"]) (simp add: \<Gamma>1 \<Gamma>2 d)
  with c_eq gl_def show "provable gl" by simp
qed

lemma p_abs_not_Closed: "p_abs \<Sigma> gl \<noteq> Closed"
proof (cases gl)
  case (Pair H c)
  then show ?thesis
    by (simp add: p_abs.simps split: option.splits tm.splits ty.splits list.splits if_splits)
qed

lemma p_abs_SubgoalsE:
  assumes "p_abs \<Sigma> (H, c) = Subgoals gs"
  obtains \<sigma> \<tau> s t where "HOL_Lite_Waterfall.dest_eq c = Some (funT \<sigma> \<tau>, Abs \<sigma> s, Abs \<sigma> t)"
    and "wf_ty \<Sigma> \<sigma>" and "closed_at (Suc 0) s" and "closed_at (Suc 0) t"
    and "gs = [(H, mk_eq \<tau> (subst_bv 0 (Fv (HOL_Lite_Waterfall.fresh_name (fv_names (c # H))) \<sigma>) s)
                            (subst_bv 0 (Fv (HOL_Lite_Waterfall.fresh_name (fv_names (c # H))) \<sigma>) t))]"
  using assms
  by (auto simp: p_abs.simps split: option.splits tm.splits ty.splits list.splits if_splits)

lemma sound_p_abs: "sound_proc (p_abs \<Sigma>)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix gl
  assume "p_abs \<Sigma> gl = Closed"
  with p_abs_not_Closed show "provable gl" by simp
next
  fix gl gs
  assume peq: "p_abs \<Sigma> gl = Subgoals gs" and prov: "\<forall>g'\<in>set gs. provable g'"
  obtain H c where gl_def: "gl = (H, c)" by (cases gl)
  define x where "x = HOL_Lite_Waterfall.fresh_name (fv_names (c # H))"
  from peq[unfolded gl_def] obtain \<sigma> \<tau> s t where
      de: "HOL_Lite_Waterfall.dest_eq c = Some (funT \<sigma> \<tau>, Abs \<sigma> s, Abs \<sigma> t)"
      and wf: "wf_ty \<Sigma> \<sigma>" and cs: "closed_at (Suc 0) s" and ct: "closed_at (Suc 0) t"
      and gs_def: "gs = [(H, mk_eq \<tau> (subst_bv 0 (Fv x \<sigma>) s) (subst_bv 0 (Fv x \<sigma>) t))]"
    unfolding x_def
    by (rule p_abs_SubgoalsE)
  from HOL_Lite_Waterfall.dest_eq_sound[OF de] have c_eq: "c = mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> s) (Abs \<sigma> t)" .
  from prov gs_def have "provable (H, mk_eq \<tau> (subst_bv 0 (Fv x \<sigma>) s) (subst_bv 0 (Fv x \<sigma>) t))"
    by simp
  from this[unfolded provable.simps] obtain \<Gamma> where hsub: "\<Gamma> \<subseteq> set H"
    and d: "derivable \<Gamma> (mk_eq \<tau> (subst_bv 0 (Fv x \<sigma>) s) (subst_bv 0 (Fv x \<sigma>) t))" by blast
  have xfresh_c: "(x, \<sigma>) \<notin> fvs c"
    unfolding x_def by (rule fresh_name_not_free) simp
  have xfresh_H: "\<forall>p\<in>\<Gamma>. (x, \<sigma>) \<notin> fvs p"
  proof
    fix p assume "p \<in> \<Gamma>"
    with hsub have "p \<in> set H" by auto
    then have "p \<in> set (c # H)" by simp
    then show "(x, \<sigma>) \<notin> fvs p" unfolding x_def by (rule fresh_name_not_free)
  qed
  from xfresh_c[unfolded c_eq] have xs: "(x, \<sigma>) \<notin> fvs s" and xt: "(x, \<sigma>) \<notin> fvs t"
    by (simp_all add: mk_eq_def)
  from derivable.abs[OF d wf xfresh_H]
  have "derivable \<Gamma> (mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> (subst_bv 0 (Fv x \<sigma>) s)))
                                       (Abs \<sigma> (abs_fv 0 x \<sigma> (subst_bv 0 (Fv x \<sigma>) t))))" .
  with abs_fv_subst_bv_id[OF cs xs] abs_fv_subst_bv_id[OF ct xt]
  have "derivable \<Gamma> (mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> s) (Abs \<sigma> t))" by simp
  with c_eq hsub gl_def show "provable gl" by (auto simp: provable.simps)
qed

lemma sound_default_procs: "\<forall>p\<in>set (default_procs \<Sigma>). sound_proc p"
  by (simp add: default_procs_def sound_p_refl sound_p_assume sound_p_assume_sym sound_p_cong sound_p_abs)

end

subsection \<open>Non-vacuity checks\<close>

text \<open>
  These examples double as end-to-end checks that the driver, the processors, and the
  freshness/closedness side conditions of @{const p_abs} compose as intended, using the
  concrete signature @{const base_hsig} from HOL_Lite_Derived.
\<close>

text \<open>(a) @{const p_refl} alone closes a reflexivity goal whose sides are equal terms
  containing both an @{const Abs} and a polymorphic instance of @{text "="}.\<close>

lemma waterfall_example_refl_poly:
  "waterfall (Suc 0) (default_procs base_hsig) ([],
     mk_eq (funT boolT boolT)
       (Abs boolT (App (App (Cst ''='' (funT boolT (funT boolT boolT))) (Bv 0)) (Fv ''p'' boolT)))
       (Abs boolT (App (App (Cst ''='' (funT boolT (funT boolT boolT))) (Bv 0)) (Fv ''p'' boolT)))) = []"
  by eval

theorem base_derivable_refl_poly:
  "base.derivable {}
     (mk_eq (funT boolT boolT)
       (Abs boolT (App (App (Cst ''='' (funT boolT (funT boolT boolT))) (Bv 0)) (Fv ''p'' boolT)))
       (Abs boolT (App (App (Cst ''='' (funT boolT (funT boolT boolT))) (Bv 0)) (Fv ''p'' boolT))))"
  using base.waterfall_prove[OF base.sound_default_procs waterfall_example_refl_poly] .

text \<open>(b) A goal needing @{const p_abs} to open the binder, @{const p_cong} to peel the
  common function, @{const p_refl} to close the function-equality subgoal and
  @{const p_assume} (resp.\ @{const p_assume_sym}) to close the argument-equality subgoal
  from a hypothesis.\<close>

lemma waterfall_example_cong_abs_assume:
  "waterfall 5 (default_procs base_hsig)
     ([mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT)],
      mk_eq (funT boolT boolT)
        (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
        (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT)))) = []"
  by eval

theorem base_derivable_cong_abs_assume:
  obtains \<Gamma> where "\<Gamma> \<subseteq> {mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT)}"
    and "base.derivable \<Gamma>
           (mk_eq (funT boolT boolT)
              (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
              (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
proof -
  have "base.provable ([mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT)],
      mk_eq (funT boolT boolT) (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
  proof (rule base.waterfall_sound[OF base.sound_default_procs])
    show "\<forall>g'\<in>set (waterfall 5 (default_procs base_hsig)
        ([mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT)],
         mk_eq (funT boolT boolT) (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                                   (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))).
        base.provable g'"
      by (simp add: waterfall_example_cong_abs_assume)
  qed
  then obtain \<Gamma> where g1: "\<Gamma> \<subseteq> {mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT)}"
      and g2: "base.derivable \<Gamma>
             (mk_eq (funT boolT boolT)
                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
    by (auto simp: base.provable.simps)
  show ?thesis by (rule that[OF g1 g2])
qed

lemma waterfall_example_cong_abs_assume_sym:
  "waterfall 5 (default_procs base_hsig)
     ([mk_eq boolT (Fv ''q'' boolT) (Fv ''p'' boolT)],
      mk_eq (funT boolT boolT)
        (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
        (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT)))) = []"
  by eval

theorem base_derivable_cong_abs_assume_sym:
  obtains \<Gamma> where "\<Gamma> \<subseteq> {mk_eq boolT (Fv ''q'' boolT) (Fv ''p'' boolT)}"
    and "base.derivable \<Gamma>
           (mk_eq (funT boolT boolT)
              (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
              (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
proof -
  have "base.provable ([mk_eq boolT (Fv ''q'' boolT) (Fv ''p'' boolT)],
      mk_eq (funT boolT boolT) (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
  proof (rule base.waterfall_sound[OF base.sound_default_procs])
    show "\<forall>g'\<in>set (waterfall 5 (default_procs base_hsig)
        ([mk_eq boolT (Fv ''q'' boolT) (Fv ''p'' boolT)],
         mk_eq (funT boolT boolT) (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                                   (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))).
        base.provable g'"
      by (simp add: waterfall_example_cong_abs_assume_sym)
  qed
  then obtain \<Gamma> where g1: "\<Gamma> \<subseteq> {mk_eq boolT (Fv ''q'' boolT) (Fv ''p'' boolT)}"
      and g2: "base.derivable \<Gamma>
             (mk_eq (funT boolT boolT)
                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''p'' boolT)))
                (Abs boolT (App (Abs boolT (Bv 0)) (Fv ''q'' boolT))))"
    by (auto simp: base.provable.simps)
  show ?thesis by (rule that[OF g1 g2])
qed

text \<open>(c) A goal none of the default processors can make progress on comes back unchanged,
  as a stable residual goal, for any amount of fuel.\<close>

lemma waterfall_example_residual:
  "waterfall 5 (default_procs base_hsig)
     ([], mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT))
   = [([], mk_eq boolT (Fv ''p'' boolT) (Fv ''q'' boolT))]"
  by eval


section \<open>Executable finite-region enumeration\<close>

fun lists_upto :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "lists_upto 0 xs = [[]]"
| "lists_upto (Suc n) xs = [[]] @ concat (map (\<lambda>x. map (Cons x) (lists_upto n xs)) xs)"

lemma set_lists_upto: "set (lists_upto n xs) = {ys. set ys \<subseteq> set xs \<and> length ys \<le> n}"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof (rule set_eqI)
    fix ys
    show "ys \<in> set (lists_upto (Suc n) xs) \<longleftrightarrow> ys \<in> {ys. set ys \<subseteq> set xs \<and> length ys \<le> Suc n}"
      using Suc.IH by (cases ys) auto
  qed
qed

fun raw_types :: "name list \<Rightarrow> nat \<Rightarrow> ty list" where
  "raw_types ns 0 = []"
| "raw_types ns (Suc k) =
     (let args = lists_upto k (raw_types ns k) in
      map TyVar ns @ concat (map (\<lambda>c. map (TyApp c) args) ns))"

lemma set_raw_types: "set (raw_types ns r) = ty_univ (set ns) r"
  by (induction r) (auto simp: set_lists_upto image_iff)

lemma ty_univ_names: "t \<in> ty_univ N r \<Longrightarrow> ty_names t \<subseteq> N"
  by (induction r arbitrary: t) (fastforce simp: subset_iff)+

definition enum_ty :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> ty list" where
  "enum_ty ns \<Sigma> r = remdups (filter (\<lambda>t. wf_ty \<Sigma> t \<and> ty_size t \<le> r) (raw_types ns r))"

lemma set_enum_ty: "set (enum_ty ns \<Sigma> r) = Ty (set ns) \<Sigma> r"
  using Ty_subset_ty_univ[of \<Sigma> _ r "set ns"]
  by (auto simp: enum_ty_def set_raw_types Ty_def dest: ty_univ_names)

fun raw_terms :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm list" where
  "raw_terms ns \<Sigma> r 0 = []"
| "raw_terms ns \<Sigma> r (Suc k) =
    (let tys = enum_ty ns \<Sigma> r; prev = raw_terms ns \<Sigma> r k in
     map (\<lambda>(x,t). Fv x t) (List.product ns tys) @
     map Bv [0..<Suc r] @
     map (\<lambda>(c,t). Cst c t) (List.product ns tys) @
     map (\<lambda>(f,a). App f a) (List.product prev prev) @
     map (\<lambda>(t,b). Abs t b) (List.product tys prev))"

lemma set_raw_terms: "set (raw_terms ns \<Sigma> r k) = tm_univ2 (set ns) \<Sigma> r k"
  by (induction k) (auto simp: set_enum_ty Let_def)

lemma raw_terms_wf: "t \<in> tm_univ2 N \<Sigma> r k \<Longrightarrow> wf_tm N \<Sigma> r t"
  by (induction k arbitrary: t) (auto simp: Ty_def)

definition enum_tm :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm list" where
  "enum_tm ns \<Sigma> r = remdups (filter (\<lambda>t. tm_size t \<le> r \<and> typeof \<Sigma> [] t \<noteq> None)
    (raw_terms ns \<Sigma> r r))"

lemma set_enum_tm: "set (enum_tm ns \<Sigma> r) = Tm_wt (set ns) \<Sigma> r"
  by (auto simp: enum_tm_def set_raw_terms Tm_wt_def Tm_def
      dest: raw_terms_wf intro: Tm_subset_tm_univ2)

fun subsets :: "'a list \<Rightarrow> 'a list list" where
  "subsets [] = [[]]"
| "subsets (x # xs) = subsets xs @ map (Cons x) (subsets xs)"

lemma set_subsets: "set (map set (subsets xs)) = Pow (set xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have eq: "Pow (insert a (set xs)) = Pow (set xs) \<union> insert a ` Pow (set xs)"
  proof (rule equalityI)
    show "Pow (insert a (set xs)) \<subseteq> Pow (set xs) \<union> insert a ` Pow (set xs)"
    proof
      fix A assume A: "A \<in> Pow (insert a (set xs))"
      show "A \<in> Pow (set xs) \<union> insert a ` Pow (set xs)"
      proof (cases "a \<in> A")
        case True
        have "A - {a} \<subseteq> set xs" using A by auto
        moreover have "A = insert a (A - {a})" using True by auto
        have "A - {a} \<in> Pow (set xs)" using \<open>A - {a} \<subseteq> set xs\<close> by simp
        then have "insert a (A - {a}) \<in> insert a ` Pow (set xs)" by (rule imageI)
        with \<open>A = insert a (A - {a})\<close> show ?thesis by simp
      next
        case False
        with A have "A \<subseteq> set xs" by (auto simp: Pow_def)
        then show ?thesis by (simp add: Pow_def)
      qed
    qed
  next
    show "Pow (set xs) \<union> insert a ` Pow (set xs) \<subseteq> Pow (insert a (set xs))" by auto
  qed
  have img: "(\<lambda>x. insert a (set x)) ` set (subsets xs) = insert a ` (set ` set (subsets xs))"
    by (simp add: image_image)
  show ?case using Cons.IH eq img by simp
qed

definition enum_seq :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "enum_seq ns \<Sigma> r = remdups (map (\<lambda>(H,c). (set H,c))
    (List.product (subsets (enum_tm ns \<Sigma> r)) (enum_tm ns \<Sigma> r)))"

lemma image_set_product:
  "(\<lambda>(H,c). (set H,c)) ` (A \<times> B) = (set ` A) \<times> B"
  by auto

lemma set_enum_seq: "set (enum_seq ns \<Sigma> r) = Sequent_r (set ns) \<Sigma> r"
  by (simp add: enum_seq_def Sequent_r_def set_enum_tm image_set_product
      set_subsets[unfolded set_map])

lemma distinct_enum_seq: "distinct (enum_seq ns \<Sigma> r)"
  by (simp add: enum_seq_def)

section \<open>Executable one-step bounded search\<close>

text \<open>
  The finite forward operators of HOL_Lite_L8 (@{text step_refl}, @{text step_trans}, ...)
  live inside the @{locale hol_lite_axs} context, so they take the fixed signature and axiom
  oracle implicitly; that keeps their statements short but means they cannot be handed to the
  code generator without an interpretation. The definitions below give a single, explicit-argument
  implementation of each rule step, executable by @{command value} or the @{text eval} proof
  method; only the soundness connection to the semantic \<open>step_*\<close> operators lives inside the
  locale. These definitions are the sole implementation of each rule step: @{text runtime_step}
  below composes them directly rather than restating the rule bodies a second time.\<close>

definition runtime_bounded :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> bool" where
  "runtime_bounded \<Sigma> ns r p =
    (fst p \<subseteq> set (enum_tm ns \<Sigma> r) \<and> snd p \<in> set (enum_tm ns \<Sigma> r))"

lemma runtime_bounded_iff [simp]:
  "runtime_bounded \<Sigma> ns r p \<longleftrightarrow> p \<in> Sequent_r (set ns) \<Sigma> r"
  by (cases p) (simp add: runtime_bounded_def Sequent_r_def set_enum_tm)

definition runtime_scan :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
  ((tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option) \<Rightarrow>
  (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "runtime_scan \<Sigma> ns r f S = concat (map (\<lambda>p1. concat (map (\<lambda>p2. case f p1 p2 of
    None \<Rightarrow> [] | Some q \<Rightarrow> if runtime_bounded \<Sigma> ns r q then [q] else []) S)) S)"

lemma set_concat_map: "set (concat (map g xs)) = (\<Union>x\<in>set xs. set (g x))"
  by (induction xs) auto

lemma set_runtime_scan:
  "set (runtime_scan \<Sigma> ns r f S) = (\<Union>p1\<in>set S. \<Union>p2\<in>set S.
    case f p1 p2 of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
proof -
  have per: "\<And>p1 p2. set (case f p1 p2 of None \<Rightarrow> []
     | Some q \<Rightarrow> if runtime_bounded \<Sigma> ns r q then [q] else []) =
     (case f p1 p2 of None \<Rightarrow> {}
     | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
  proof -
    fix p1 p2
    show "set (case f p1 p2 of None \<Rightarrow> []
       | Some q \<Rightarrow> if runtime_bounded \<Sigma> ns r q then [q] else []) =
       (case f p1 p2 of None \<Rightarrow> {}
       | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
      by (cases "f p1 p2") simp_all
  qed
  show ?thesis unfolding runtime_scan_def
    using per by (simp only: set_concat_map)
qed

definition exec_refl :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_refl \<Sigma> ns r = concat (map (\<lambda>t. case typeof \<Sigma> [] t of
    Some \<tau> \<Rightarrow> (let q = ({}, mk_eq \<tau> t t) in if runtime_bounded \<Sigma> ns r q then [q] else [])
  | None \<Rightarrow> []) (enum_tm ns \<Sigma> r))"

definition exec_assm :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_assm \<Sigma> ns r = concat (map (\<lambda>p. if typeof \<Sigma> [] p = Some boolT \<and>
    runtime_bounded \<Sigma> ns r ({p}, p) then [({p},p)] else []) (enum_tm ns \<Sigma> r))"

definition exec_beta :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list" where
  "exec_beta \<Sigma> ns r = concat (map (\<lambda>w. concat (map (\<lambda>x.
    case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (let q = ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) in
         if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
      | _ \<Rightarrow> [])
    | _ \<Rightarrow> []) ns)) (enum_tm ns \<Sigma> r))"

definition exec_axiom :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) list" where
  "exec_axiom \<Sigma> axs ns r = concat (map (\<lambda>p. if runtime_bounded \<Sigma> ns r ({},p)
    then [({},p)] else []) (axs (set ns) r))"

definition exec_trans :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_trans \<Sigma> ns r S = runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
    case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
    | _ \<Rightarrow> None) S"

definition exec_mk_comb :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_mk_comb \<Sigma> ns r S = runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
    case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
        then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
    | _ \<Rightarrow> None) S"

definition exec_eq_mp :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_eq_mp \<Sigma> ns r S = runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
    case dest_eq (snd p1) of
      Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p
        then Some (fst p1 \<union> fst p2,q) else None
    | None \<Rightarrow> None) S"

definition exec_deduct_antisym :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_deduct_antisym \<Sigma> ns r S = runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
    Some ((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2))) S"

definition exec_abs :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_abs \<Sigma> ns r S = concat (map (\<lambda>p1. concat (map (\<lambda>\<sigma>. concat (map (\<lambda>x.
    case HOL_Lite_Waterfall.dest_eq (snd p1) of
      Some (\<tau>,s,t) \<Rightarrow>
        (let q = (fst p1, mk_eq (funT \<sigma> \<tau>)
           (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) in
         if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
    | None \<Rightarrow> []) (HOL_Lite_Waterfall.fresh_name ns # ns))) (enum_ty ns \<Sigma> r))) S)"

subsection \<open>Type-variable instantiation enumerators\<close>

fun inst_envs :: "name list \<Rightarrow> ty list \<Rightarrow> (name \<times> ty) list list" where
  "inst_envs [] tys = [[]]"
| "inst_envs (v # vs) tys = concat (map (\<lambda>\<tau>.
     map (Cons (v,\<tau>)) (inst_envs vs tys)) tys)"

lemma set_inst_envs:
  "set (inst_envs vs tys) = {e. map fst e = vs \<and> set (map snd e) \<subseteq> set tys}"
proof (induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  show ?case
  proof (rule set_eqI)
    fix e
    show "e \<in> set (inst_envs (a # vs) tys) \<longleftrightarrow>
      e \<in> {e. map fst e = a # vs \<and> set (map snd e) \<subseteq> set tys}"
    proof (cases e)
      case Nil
      then show ?thesis by auto
    next
      case (Cons h tail)
      obtain v \<tau> where h: "h = (v,\<tau>)" by (cases h) auto
      show ?thesis using Cons.IH
        by (auto simp: Cons h image_iff)
    qed
  qed
qed

lemma map_of_range: "map_of e a = Some t \<Longrightarrow> t \<in> set (map snd e)"
  by (induction e) (auto split: if_splits)

lemma map_of_mapped_distinct:
  "distinct vs \<Longrightarrow> map_of (map (\<lambda>v. (v, f v)) vs) a =
    (if a \<in> set vs then Some (f a) else None)"
  by (induction vs) auto

lemma inst_envs_PiE:
  assumes distinct: "distinct vs" and vs: "set vs = V"
  shows "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)} =
         {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}"
proof (rule equalityI)
  show "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)} \<subseteq>
         {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}"
  proof
    fix \<theta> assume "\<theta> \<in> {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}"
    then obtain e where e: "e \<in> set (inst_envs vs tys)"
      and \<theta>: "\<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)" by blast
    have dom: "map fst e = vs" and ran: "set (map snd e) \<subseteq> set tys"
      using e by (auto simp: set_inst_envs)
    have lookup_iff: "\<And>a. map_of e a = None \<longleftrightarrow> a \<notin> V"
      using dom vs by (metis map_of_eq_None_iff set_map)
    let ?f = "restrict (\<lambda>a. the (map_of e a)) V"
    have range: "\<And>a. a \<in> V \<Longrightarrow> the (map_of e a) \<in> set tys"
    proof -
      fix a assume "a \<in> V"
      then have "map_of e a \<noteq> None" using lookup_iff by blast
      then obtain t where hit: "map_of e a = Some t" by (cases "map_of e a") auto
      from map_of_range[OF hit] ran hit show "the (map_of e a) \<in> set tys" by auto
    qed
    have f: "?f \<in> PiE V (\<lambda>_. set tys)"
      using range by (auto intro!: PiE_I)
    have "\<theta> = (\<lambda>a. if a \<in> V then ?f a else boolT)"
    proof (rule ext)
      fix a
      show "\<theta> a = (if a \<in> V then ?f a else boolT)"
      proof (cases "a \<in> V")
        case True
        with lookup_iff obtain t where "map_of e a = Some t"
          by (cases "map_of e a") auto
        with True \<theta> show ?thesis by (simp add: restrict_apply)
      next
        case False
        then have "map_of e a = None" using lookup_iff by blast
        with False \<theta> show ?thesis by simp
      qed
    qed
    with f show "\<theta> \<in> {(\<lambda>a. if a \<in> V then f a else boolT) |f.
              f \<in> PiE V (\<lambda>_. set tys)}" by blast
  qed
next
  show "{(\<lambda>a. if a \<in> V then f a else boolT) |f. f \<in> PiE V (\<lambda>_. set tys)} \<subseteq>
        {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}"
  proof
    fix \<theta> assume "\<theta> \<in> {(\<lambda>a. if a \<in> V then f a else boolT) |f. f \<in> PiE V (\<lambda>_. set tys)}"
    then obtain f where f: "f \<in> PiE V (\<lambda>_. set tys)"
      and \<theta>: "\<theta> = (\<lambda>a. if a \<in> V then f a else boolT)" by blast
    let ?e = "map (\<lambda>v. (v,f v)) vs"
    have e: "?e \<in> set (inst_envs vs tys)"
      using f vs by (auto simp: set_inst_envs PiE_iff o_def)
    have "\<theta> = (\<lambda>a. case map_of ?e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)"
      by (simp add: \<theta> vs map_of_mapped_distinct[OF distinct] fun_eq_iff)
    with e show "\<theta> \<in> {(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
              e \<in> set (inst_envs vs tys)}" by blast
  qed
qed

definition inst_vars :: "(tm set \<times> tm) \<Rightarrow> name set" where
  "inst_vars p = tm_tyvars (snd p) \<union> (\<Union>t\<in>fst p. tm_tyvars t)"

fun tyvar_list :: "ty \<Rightarrow> name list" where
  "tyvar_list (TyVar a) = [a]"
| "tyvar_list (TyApp c ts) = concat (map tyvar_list ts)"

fun tm_tyvar_list :: "tm \<Rightarrow> name list" where
  "tm_tyvar_list (Fv x \<tau>) = tyvar_list \<tau>"
| "tm_tyvar_list (Bv i) = []"
| "tm_tyvar_list (Cst c \<tau>) = tyvar_list \<tau>"
| "tm_tyvar_list (App f a) = tm_tyvar_list f @ tm_tyvar_list a"
| "tm_tyvar_list (Abs \<tau> b) = tyvar_list \<tau> @ tm_tyvar_list b"

lemma set_tyvar_list [simp]: "set (tyvar_list \<tau>) = ty_tyvars \<tau>"
  by (induction \<tau> rule: ty.induct) auto

lemma set_tm_tyvar_list [simp]: "set (tm_tyvar_list t) = tm_tyvars t"
  by (induction t rule: tm.induct) auto

definition inst_var_list :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> name list" where
  "inst_var_list \<Sigma> ns r p = remdups (tm_tyvar_list (snd p) @
    concat (map tm_tyvar_list (filter (\<lambda>t. t \<in> fst p) (enum_tm ns \<Sigma> r))))"

lemma set_inst_var_list:
  "p \<in> Sequent_r (set ns) \<Sigma> r \<Longrightarrow> set (inst_var_list \<Sigma> ns r p) = inst_vars p"
  by (auto simp: inst_var_list_def inst_vars_def Sequent_r_def set_enum_tm)

lemma distinct_inst_var_list [simp]: "distinct (inst_var_list \<Sigma> ns r p)"
  by (simp add: inst_var_list_def)

definition exec_inst_type :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "exec_inst_type \<Sigma> ns r S = concat (map (\<lambda>p1.
    concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))
      in if runtime_bounded \<Sigma> ns r q then [q] else [])
      (inst_envs (inst_var_list \<Sigma> ns r p1) (enum_ty ns \<Sigma> r)))) S)"

lemma Max_lengths: "Max (insert 0 (length ` set ns)) =
  foldr (\<lambda>n acc. max (length n) acc) ns 0"
proof (induction ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  have "Max (insert 0 (length ` set (a # ns))) =
    Max (insert (length a) (insert 0 (length ` set ns)))"
    by (simp add: insert_commute)
  also have "... = max (length a) (Max (insert 0 (length ` set ns)))"
    by (simp add: Max_insert)
  finally show ?case using Cons.IH by simp
qed

lemma case_guarded_result [simp]:
  "(case (if P then Some q else None) of None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}) =
     (if P \<and> q \<in> Q then {q} else {})"
  by simp

lemma case_option_result [simp]:
  "(case (case z of None \<Rightarrow> None | Some y \<Rightarrow> f y) of
       None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}) =
    (case z of None \<Rightarrow> {} | Some y \<Rightarrow>
      (case f y of None \<Rightarrow> {} | Some x \<Rightarrow> if x \<in> Q then {x} else {}))"
  by (cases z) simp_all

context hol_lite_axs
begin

lemma runtime_fresh_eq:
  "HOL_Lite_Waterfall.fresh_name ns = fresh_name (set ns)"
  by (simp add: HOL_Lite_Waterfall.fresh_name_def fresh_name_def Max_lengths)

lemma runtime_dest_eq: "HOL_Lite_Waterfall.dest_eq t = dest_eq t"
  by (induction t rule: HOL_Lite_Waterfall.dest_eq.induct)
     (auto simp: dest_eq_def split: tm.splits ty.splits list.splits if_splits)

lemma set_exec_refl: "set (exec_refl \<Sigma> ns r) = step_refl (set ns) r"
proof -
  have per: "\<And>t. set (case typeof \<Sigma> [] t of
      Some \<tau> \<Rightarrow> (let q = ({}, mk_eq \<tau> t t) in if runtime_bounded \<Sigma> ns r q then [q] else [])
    | None \<Rightarrow> []) = (case typeof \<Sigma> [] t of
      Some \<tau> \<Rightarrow> (if ({}, mk_eq \<tau> t t) \<in> Sequent_r (set ns) \<Sigma> r
                 then {({}, mk_eq \<tau> t t)} else {})
    | None \<Rightarrow> {})"
    by (simp add: Let_def split: option.splits)
  show ?thesis unfolding exec_refl_def step_refl_def
    using per by (simp add: set_enum_tm)
qed

lemma set_exec_assm: "set (exec_assm \<Sigma> ns r) = step_assm (set ns) r"
  by (auto simp: exec_assm_def step_assm_def set_enum_tm runtime_bounded_iff)

lemma set_exec_axiom: "set (exec_axiom \<Sigma> axs ns r) = step_axiom (set ns) r"
  by (auto simp: exec_axiom_def step_axiom_def runtime_bounded_iff)

lemma set_exec_trans: "set (exec_trans \<Sigma> ns r S) = step_trans (set ns) r (set S)"
proof -
  have per: "\<And>p1 p2. (case (case (HOL_Lite_Waterfall.dest_eq (snd p1), HOL_Lite_Waterfall.dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
      | _ \<Rightarrow> None) of
      None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
        if \<tau>' = \<tau> \<and> t' = t \<and>
           (fst p1 \<union> fst p2, mk_eq \<tau> s u) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2, mk_eq \<tau> s u)} else {}
      | _ \<Rightarrow> {})"
    by (simp add: runtime_dest_eq split: option.splits prod.splits if_splits)
  show ?thesis unfolding exec_trans_def set_runtime_scan step_trans_def
    using per by simp
qed

lemma set_exec_mk_comb: "set (exec_mk_comb \<Sigma> ns r S) = step_mk_comb (set ns) r (set S)"
proof -
  have per: "\<And>p1 p2. (case (case (HOL_Lite_Waterfall.dest_eq (snd p1), HOL_Lite_Waterfall.dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
        then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
    | _ \<Rightarrow> None) of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case (dest_eq (snd p1), dest_eq (snd p2)) of
      (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
        if fn = ''fun'' \<and> \<sigma>0 = \<sigma> \<and>
           (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b))} else {}
    | _ \<Rightarrow> {})"
    by (simp add: runtime_dest_eq split: option.splits prod.splits ty.splits list.splits if_splits)
  show ?thesis unfolding exec_mk_comb_def set_runtime_scan step_mk_comb_def
    using per by simp
qed

lemma set_exec_eq_mp: "set (exec_eq_mp \<Sigma> ns r S) = step_eq_mp (set ns) r (set S)"
proof -
  have per: "\<And>p1 p2. (case (case HOL_Lite_Waterfall.dest_eq (snd p1) of
    Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p then Some (fst p1 \<union> fst p2,q) else None
    | None \<Rightarrow> None) of None \<Rightarrow> {} | Some q \<Rightarrow> if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}) =
    (case dest_eq (snd p1) of
      Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p \<and>
        (fst p1 \<union> fst p2,q) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1 \<union> fst p2,q)} else {}
    | None \<Rightarrow> {})"
    by (simp add: runtime_dest_eq split: option.splits prod.splits if_splits)
  show ?thesis unfolding exec_eq_mp_def set_runtime_scan step_eq_mp_def
    using per by simp
qed

lemma set_exec_deduct_antisym:
  "set (exec_deduct_antisym \<Sigma> ns r S) = step_deduct_antisym (set ns) r (set S)"
  unfolding exec_deduct_antisym_def set_runtime_scan step_deduct_antisym_def by simp

lemma set_exec_beta: "set (exec_beta \<Sigma> ns r) = step_beta (set ns) r"
proof -
  have per: "\<And>w x. set (case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (let q = ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) in
         if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
      | _ \<Rightarrow> []) | _ \<Rightarrow> []) =
    (case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
      Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
        (if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and>
          ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) \<in> Sequent_r (set ns) \<Sigma> r
         then {({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b))} else {})
      | _ \<Rightarrow> {}) | _ \<Rightarrow> {})"
    by (simp add: Let_def split: tm.splits option.splits ty.splits list.splits if_splits)
  show ?thesis unfolding exec_beta_def step_beta_def
    using per by (simp add: set_enum_tm set_concat_map)
qed

lemma set_exec_abs: "set (exec_abs \<Sigma> ns r S) = step_abs (set ns) r (set S)"
proof -
  have per: "\<And>p1 \<sigma> x. set (case HOL_Lite_Waterfall.dest_eq (snd p1) of
      Some (\<tau>,s,t) \<Rightarrow>
        (let q = (fst p1, mk_eq (funT \<sigma> \<tau>)
           (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) in
         if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
    | None \<Rightarrow> []) =
    (case dest_eq (snd p1) of Some (\<tau>,s,t) \<Rightarrow>
       (if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and>
          (fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s))
            (Abs \<sigma> (abs_fv 0 x \<sigma> t))) \<in> Sequent_r (set ns) \<Sigma> r
        then {(fst p1, mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> (abs_fv 0 x \<sigma> s))
            (Abs \<sigma> (abs_fv 0 x \<sigma> t)))} else {})
    | None \<Rightarrow> {})"
    by (simp add: Let_def runtime_dest_eq split: option.splits)
  show ?thesis unfolding exec_abs_def step_abs_def
    using per by (simp add: set_enum_ty set_concat_map runtime_fresh_eq)
qed

lemma set_exec_inst_type:
  assumes sub: "set S \<subseteq> Sequent_r (set ns) \<Sigma> r"
  shows "set (exec_inst_type \<Sigma> ns r S) = step_inst_type (set ns) r (set S)"
proof -
  have per: "\<And>p. p \<in> set S \<Longrightarrow>
    set (concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if runtime_bounded \<Sigma> ns r q then [q] else [])
      (inst_envs (inst_var_list \<Sigma> ns r p) (enum_ty ns \<Sigma> r)))) =
    (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
      let \<theta> = (\<lambda>a. if a \<in> inst_vars p then f a else boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
  proof -
    fix p assume p: "p \<in> set S"
    have var: "set (inst_var_list \<Sigma> ns r p) = inst_vars p"
      using p sub set_inst_var_list by blast
    have env_eq:
      "{(\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT) |e.
           e \<in> set (inst_envs (inst_var_list \<Sigma> ns r p) (enum_ty ns \<Sigma> r))} =
       {(\<lambda>a. if a \<in> inst_vars p then f a else boolT) |f.
           f \<in> PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r)}"
      using inst_envs_PiE[OF distinct_inst_var_list var, of "enum_ty ns \<Sigma> r"]
      by (simp add: set_enum_ty)
    have idx: "\<And>F. (\<Union>e\<in>set (inst_envs (inst_var_list \<Sigma> ns r p) (enum_ty ns \<Sigma> r)).
       F (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT)) =
       (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
       F (\<lambda>a. if a \<in> inst_vars p then f a else boolT))"
    proof -
      fix F
      let ?E = "set (inst_envs (inst_var_list \<Sigma> ns r p) (enum_ty ns \<Sigma> r))"
      let ?P = "PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r)"
      let ?g = "\<lambda>e a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT"
      let ?h = "\<lambda>f a. if a \<in> inst_vars p then f a else boolT"
      have equal: "?g ` ?E = ?h ` ?P" using env_eq by auto
      have "(\<Union>e\<in>?E. F (?g e)) = (\<Union>\<theta>\<in>?g ` ?E. F \<theta>)" by auto
      also have "... = (\<Union>\<theta>\<in>?h ` ?P. F \<theta>)" using equal by simp
      also have "... = (\<Union>f\<in>?P. F (?h f))" by auto
      finally show "(\<Union>e\<in>?E. F (?g e)) = (\<Union>f\<in>?P. F (?h f))" .
    qed
    show "set (concat (map (\<lambda>e.
      let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if runtime_bounded \<Sigma> ns r q then [q] else [])
      (inst_envs (inst_var_list \<Sigma> ns r p) (enum_ty ns \<Sigma> r)))) =
      (\<Union>f\<in>PiE (inst_vars p) (\<lambda>_. Ty (set ns) \<Sigma> r).
      let \<theta> = (\<lambda>a. if a \<in> inst_vars p then f a else boolT);
          q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
      in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {})"
      using idx[of "\<lambda>\<theta>. let q = (tinst \<theta> ` fst p, tinst \<theta> (snd p))
        in if q \<in> Sequent_r (set ns) \<Sigma> r then {q} else {}"]
      by (simp add: set_concat_map Let_def)
  qed
  show ?thesis unfolding exec_inst_type_def step_inst_type_def inst_vars_def
    using per by (simp add: set_concat_map Let_def inst_vars_def)
qed

end

section \<open>Global executable bounded-step driver\<close>

text \<open>@{text runtime_step} composes the ten rule-step functions above into the single
  global, explicit-argument executable step used by the bounded waterfall driver below.
  Since every rule step is already global (see the previous section), no second copy of
  the rule bodies is needed here: this definition is a thin composition, not a restatement.\<close>

definition runtime_step :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
  (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "runtime_step \<Sigma> axs ns r S = remdups (
     exec_refl \<Sigma> ns r @ exec_assm \<Sigma> ns r @ exec_beta \<Sigma> ns r @ exec_axiom \<Sigma> axs ns r @
     exec_trans \<Sigma> ns r S @ exec_mk_comb \<Sigma> ns r S @ exec_abs \<Sigma> ns r S @
     exec_eq_mp \<Sigma> ns r S @ exec_deduct_antisym \<Sigma> ns r S @ exec_inst_type \<Sigma> ns r S)"

context hol_lite_axs
begin

lemma set_runtime_step:
  "set S \<subseteq> Sequent_r (set ns) \<Sigma> r \<Longrightarrow>
   set (runtime_step \<Sigma> axs ns r S) = step_r (set ns) r (set S)"
  unfolding runtime_step_def step_r_def
  by (simp add: set_exec_refl set_exec_assm set_exec_beta set_exec_axiom
      set_exec_trans set_exec_mk_comb set_exec_abs set_exec_eq_mp
      set_exec_deduct_antisym set_exec_inst_type Un_assoc)

end

section \<open>Executable complete bounded waterfall\<close>

text \<open>Supply a finite list of names, a size radius, and a terminating axiom enumerator
  satisfying the locale axiom specification. bounded_decide decides precisely the
  clipped derivations in that region; bounded_processor closes such goals in the
  existing waterfall. A region with m well-typed terms contains 2^m * m sequents,
  so the worst-case bound is large. Iteration stops as soon as no new sequent is
  generated. This is not a decision procedure for unbounded derivability.\<close>

fun bounded_rounds :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "bounded_rounds \<Sigma> axs ns r 0 S = S"
| "bounded_rounds \<Sigma> axs ns r (Suc k) S =
    (let T = remdups (S @ runtime_step \<Sigma> axs ns r S)
     in if set T = set S then S else bounded_rounds \<Sigma> axs ns r k T)"

definition bounded_bound :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> nat" where
  "bounded_bound \<Sigma> ns r = 2 ^ length (enum_tm ns \<Sigma> r) * length (enum_tm ns \<Sigma> r)"

definition bounded_decide :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) \<Rightarrow> bool" where
  "bounded_decide \<Sigma> axs ns r p =
    (p \<in> set (bounded_rounds \<Sigma> axs ns r (bounded_bound \<Sigma> ns r) []))"

definition bounded_processor :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> processor" where
  "bounded_processor \<Sigma> axs ns r g =
    (if bounded_decide \<Sigma> axs ns r (set (fst g), snd g) then Closed else Unchanged)"

context hol_lite_axs
begin

lemma set_bounded_rounds:
  assumes sub: "set S \<subseteq> Sequent_r (set ns) \<Sigma> r"
  shows "set (bounded_rounds \<Sigma> axs ns r k S) = (grow_r (set ns) r ^^ k) (set S)"
  using sub
proof (induction k arbitrary: S)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?T = "remdups (S @ runtime_step \<Sigma> axs ns r S)"
  have Tset: "set ?T = grow_r (set ns) r (set S)"
    using set_runtime_step[OF Suc.prems] by (simp add: grow_r_def)
  have Tsub: "set ?T \<subseteq> Sequent_r (set ns) \<Sigma> r"
    using Tset grow_r_subset Suc.prems by blast
  show ?case
  proof (cases "set ?T = set S")
    case True
    have fixed: "grow_r (set ns) r (set S) = set S" using Tset True by simp
    have pow: "\<And>j. (grow_r (set ns) r ^^ j) (set S) = set S"
    proof -
      fix j show "(grow_r (set ns) r ^^ j) (set S) = set S"
        by (induction j) (simp_all add: fixed funpow_Suc_right)
    qed
    show ?thesis using True fixed pow[of k]
      by (simp add: Let_def funpow_Suc_right)
  next
    case False
    have "set (bounded_rounds \<Sigma> axs ns r (Suc k) S) = (grow_r (set ns) r ^^ k) (set ?T)"
      using False Suc.IH[OF Tsub] by (simp add: Let_def)
    also have "... = (grow_r (set ns) r ^^ Suc k) (set S)"
      by (simp only: Tset funpow_Suc_right o_apply)
    finally show ?thesis .
  qed
qed

lemma bounded_bound_card:
  "bounded_bound \<Sigma> ns r = card (Sequent_r (set ns) \<Sigma> r)"
proof -
  have distinct: "distinct (enum_tm ns \<Sigma> r)" by (simp add: enum_tm_def)
  show ?thesis
    by (simp add: bounded_bound_def Sequent_r_def set_enum_tm[symmetric] distinct card_Pow distinct_card)
qed

theorem bounded_decide_iff_bderiv:
  "bounded_decide \<Sigma> axs ns r p \<longleftrightarrow> bderiv (set ns) r p"
  using set_bounded_rounds[of "[]" ns r "bounded_bound \<Sigma> ns r"]
    bounded_iteration_iff_bderiv[of "set ns" p r]
  by (simp add: bounded_decide_def bounded_bound_card iterate_r_def)

corollary bounded_decide_sound:
  "bounded_decide \<Sigma> axs ns r (\<Gamma>,c) \<Longrightarrow> derivable \<Gamma> c"
  using bounded_decide_iff_bderiv bderiv_sound by blast

lemma sound_bounded_processor: "sound_proc (bounded_processor \<Sigma> axs ns r)"
  unfolding sound_proc_def bounded_processor_def
  using bounded_decide_sound by (auto simp: provable_iff)

lemma bounded_waterfall_complete:
  "waterfall 1 [bounded_processor \<Sigma> axs ns r] (H,c) = [] \<longleftrightarrow>
   bderiv (set ns) r (set H,c)"
  by (simp add: bounded_processor_def bounded_decide_iff_bderiv)

end

end
