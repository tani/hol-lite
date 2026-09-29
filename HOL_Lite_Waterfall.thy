theory HOL_Lite_Waterfall
  imports HOL_Lite_Check HOL_Lite_Derived
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
      de: "dest_eq c = Some (\<tau>, s, s)" and ty: "typeof \<Sigma> [] s = Some \<tau>"
    by (auto simp: p_refl.simps split: option.splits if_splits)
  from dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> s s" .
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
      de: "dest_eq c = Some (\<tau>, s, t)"
      and mem: "mk_eq \<tau> t s \<in> set H" and ty: "typeof \<Sigma> [] (mk_eq \<tau> t s) = Some boolT"
    by (auto simp: p_assume_sym.simps split: option.splits if_splits)
  from dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> s t" .
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
  obtains \<tau> f a g b \<sigma> where "dest_eq c = Some (\<tau>, App f a, App g b)"
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
      de: "dest_eq c = Some (\<tau>, App f a, App g b)"
      and ty: "typeof \<Sigma> [] a = Some \<sigma>"
      and gs_def: "gs = [(H, mk_eq (funT \<sigma> \<tau>) f g), (H, mk_eq \<sigma> a b)]"
    by (rule p_cong_SubgoalsE)
  from dest_eq_sound[OF de] have c_eq: "c = mk_eq \<tau> (App f a) (App g b)" .
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
  obtains \<sigma> \<tau> s t where "dest_eq c = Some (funT \<sigma> \<tau>, Abs \<sigma> s, Abs \<sigma> t)"
    and "wf_ty \<Sigma> \<sigma>" and "closed_at (Suc 0) s" and "closed_at (Suc 0) t"
    and "gs = [(H, mk_eq \<tau> (subst_bv 0 (Fv (fresh_name (fv_names (c # H))) \<sigma>) s)
                            (subst_bv 0 (Fv (fresh_name (fv_names (c # H))) \<sigma>) t))]"
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
  define x where "x = fresh_name (fv_names (c # H))"
  from peq[unfolded gl_def] obtain \<sigma> \<tau> s t where
      de: "dest_eq c = Some (funT \<sigma> \<tau>, Abs \<sigma> s, Abs \<sigma> t)"
      and wf: "wf_ty \<Sigma> \<sigma>" and cs: "closed_at (Suc 0) s" and ct: "closed_at (Suc 0) t"
      and gs_def: "gs = [(H, mk_eq \<tau> (subst_bv 0 (Fv x \<sigma>) s) (subst_bv 0 (Fv x \<sigma>) t))]"
    unfolding x_def
    by (rule p_abs_SubgoalsE)
  from dest_eq_sound[OF de] have c_eq: "c = mk_eq (funT \<sigma> \<tau>) (Abs \<sigma> s) (Abs \<sigma> t)" .
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


end
