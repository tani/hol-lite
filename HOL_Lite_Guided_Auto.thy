theory HOL_Lite_Guided_Auto
  imports HOL_Lite_Guided_Flood
begin

section \<open>Backward decomposition and guided flood, with the flood guarantee kept\<close>

text \<open>
  @{text HOL_Lite_Waterfall} works backwards from the goal: @{text refl}, @{text assume},
  @{text assume_sym}, @{text cong} and @{text abs} close or decompose it.  What is left needs
  forward reasoning, so a guided flood is added as a processor that sees only a universe generated
  from the residual goal itself.

  The flood's guarantee is kept by staging.  The heuristic stages (backward decomposition, then
  the guided flood on a generated universe) are shortcuts: they are sound, but a decomposition can
  turn a derivable goal into a non-derivable subgoal (when axioms are present), so they are not
  complete.  The last stage is the flood over the full region @{text "Tm_wt N \<Sigma> r"}, which is
  complete in the limit: a goal that is provable is closed for some @{text "(ns, r)"}
  (@{text g_full_complete}).  Sufficiently much computation therefore always decides a provable
  goal; the heuristics only make the usual case fast.
\<close>

subsection \<open>Generating a universe from a goal\<close>

fun ty_name_list :: "ty \<Rightarrow> name list" where
  "ty_name_list (TyVar a) = [a]"
| "ty_name_list (TyApp c ts) = c # concat (map ty_name_list ts)"

fun tm_name_list :: "tm \<Rightarrow> name list" where
  "tm_name_list (Fv x \<tau>) = x # ty_name_list \<tau>"
| "tm_name_list (Bv i) = []"
| "tm_name_list (Cst c \<tau>) = c # ty_name_list \<tau>"
| "tm_name_list (App f a) = tm_name_list f @ tm_name_list a"
| "tm_name_list (Abs \<tau> b) = ty_name_list \<tau> @ tm_name_list b"

fun subtms :: "tm \<Rightarrow> tm list" where
  "subtms (Fv x \<tau>) = [Fv x \<tau>]"
| "subtms (Bv i) = [Bv i]"
| "subtms (Cst c \<tau>) = [Cst c \<tau>]"
| "subtms (App f a) = App f a # (subtms f @ subtms a)"
| "subtms (Abs \<tau> b) = Abs \<tau> b # subtms b"

definition eq_parts :: "tm list \<Rightarrow> (ty \<times> tm \<times> tm) list" where
  "eq_parts L = concat (map (\<lambda>t. case HOL_Lite_Waterfall.dest_eq t of
      Some e \<Rightarrow> [e] | None \<Rightarrow> []) L)"

text \<open>
  The standard derivation of @{text "y = x"} from @{text "x = y"} passes through
  @{text "(=) = (=)"}, @{text "(=) x = (=) y"}, @{text "x = x"} and @{text "(x = x) = (y = x)"}.
\<close>

definition sym_support :: "ty \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm list" where
  "sym_support \<tau> x y =
     (let eqc = Cst ''='' (funT \<tau> (funT \<tau> boolT)) in
      [mk_eq (funT \<tau> (funT \<tau> boolT)) eqc eqc, mk_eq (funT \<tau> boolT) (App eqc x) (App eqc y),
       mk_eq \<tau> x x, mk_eq boolT (mk_eq \<tau> x x) (mk_eq \<tau> y x), mk_eq \<tau> y x])"

definition trans_close :: "(ty \<times> tm \<times> tm) list \<Rightarrow> tm list" where
  "trans_close E = concat (map (\<lambda>(\<tau>, x, y). concat (map (\<lambda>(\<tau>', y', z).
      if \<tau>' = \<tau> \<and> y' = y then [mk_eq \<tau> x z] else []) E)) E)"

definition auto_step :: "tm list \<Rightarrow> tm list" where
  "auto_step L =
     (let E = eq_parts L;
          L1 = L @ concat (map (\<lambda>(\<tau>, x, y). sym_support \<tau> x y) E);
          E1 = eq_parts L1
      in remdups (L1 @ trans_close E1))"

fun auto_universe :: "nat \<Rightarrow> goal \<Rightarrow> tm list" where
  "auto_universe 0 g = remdups (concat (map subtms (snd g # fst g)))"
| "auto_universe (Suc k) g = auto_step (auto_universe k g)"

subsection \<open>A processor for any pair of universes\<close>

definition g_flood_result :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> (tm set \<times> tm) list" where
  "g_flood_result \<Sigma> axs ns r Hs U =
     (let H = g_universe \<Sigma> ns r Hs; W = g_universe \<Sigma> ns r U
      in g_rounds \<Sigma> axs ns r H W (g_bound H W) [])"

lemma gflood_decide_eq_result:
  "gflood_decide \<Sigma> axs ns r Hs U p \<longleftrightarrow> p \<in> set (g_flood_result \<Sigma> axs ns r Hs U)"
  by (simp add: gflood_decide_def g_flood_result_def Let_def)

text \<open>
  The processor closes a goal @{text "(H, c)"} when the flood derives @{text c} from some subset
  of the goal's hypotheses.
\<close>

definition g_processor :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> processor" where
  "g_processor \<Sigma> axs ns r Hs U g =
     (if list_ex (\<lambda>q. snd q = snd g \<and> (\<forall>h\<in>fst q. h \<in> set (fst g)))
                 (g_flood_result \<Sigma> axs ns r Hs U)
      then Closed else Unchanged)"

text \<open>The heuristic instance: the universe and the names are generated from the goal.\<close>

definition g_auto_processor :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> nat \<Rightarrow> processor" where
  "g_auto_processor \<Sigma> axs k g =
     (let U = auto_universe k g;
          ns = remdups (concat (map tm_name_list U));
          r = foldr max (map tm_size U) 0
      in g_processor \<Sigma> axs ns r (fst g) U g)"

text \<open>The complete instance: both universes are the full region.\<close>

definition g_full_processor :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    processor" where
  "g_full_processor \<Sigma> axs ns r = g_processor \<Sigma> axs ns r (enum_tm ns \<Sigma> r) (enum_tm ns \<Sigma> r)"

text \<open>
  One attempt: the backward waterfall with the guided flood at its end, or else the full flood.
\<close>

definition g_prove :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> nat \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    goal \<Rightarrow> bool" where
  "g_prove \<Sigma> axs k ns r n g =
     (waterfall n (default_procs \<Sigma> @ [g_auto_processor \<Sigma> axs k]) g = [] \<or>
      g_full_processor \<Sigma> axs ns r g = Closed)"

context hol_lite_axs
begin

lemma g_flood_result_derivable:
  assumes "q \<in> set (g_flood_result \<Sigma> axs ns r Hs U)"
  shows "derivable (fst q) (snd q)"
proof -
  define H where "H = g_universe \<Sigma> ns r Hs"
  define W where "W = g_universe \<Sigma> ns r U"
  have Ht: "set H \<subseteq> Tm_wt (set ns) \<Sigma> r" unfolding H_def by (simp add: set_g_universe)
  have Wt: "set W \<subseteq> Tm_wt (set ns) \<Sigma> r" unfolding W_def by (simp add: set_g_universe)
  have q: "q \<in> set (g_rounds \<Sigma> axs ns r H W (g_bound H W) [])"
    using assms unfolding g_flood_result_def Let_def H_def W_def .
  have "\<forall>x\<in>set (g_rounds \<Sigma> axs ns r H W (g_bound H W) []). gderiv (set H) (set W) x"
    by (rule g_rounds_sound[OF Ht Wt]) simp
  with q have gq: "gderiv (set H) (set W) q" by blast
  obtain G c where qe: "q = (G, c)" by (cases q) auto
  from gq qe have "gderiv (set H) (set W) (G, c)" by simp
  then have "derivable G c" by (rule gderiv_sound)
  then show ?thesis using qe by simp
qed

lemma sound_g_processor: "sound_proc (g_processor \<Sigma> axs ns r Hs U)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix g assume "g_processor \<Sigma> axs ns r Hs U g = Closed"
  then have "list_ex (\<lambda>q. snd q = snd g \<and> (\<forall>h\<in>fst q. h \<in> set (fst g)))
                     (g_flood_result \<Sigma> axs ns r Hs U)"
    by (simp add: g_processor_def split: if_splits)
  then obtain q where q: "q \<in> set (g_flood_result \<Sigma> axs ns r Hs U)" "snd q = snd g"
    "\<forall>h\<in>fst q. h \<in> set (fst g)" by (auto simp: list_ex_iff)
  from g_flood_result_derivable[OF q(1)] q(2) have "derivable (fst q) (snd g)" by simp
  moreover have "fst q \<subseteq> set (fst g)" using q(3) by auto
  ultimately show "provable g" by (auto simp: provable_iff)
next
  fix g gs assume "g_processor \<Sigma> axs ns r Hs U g = Subgoals gs" "\<forall>g'\<in>set gs. provable g'"
  then show "provable g" by (simp add: g_processor_def split: if_splits)
qed

lemma sound_proc_Closed:
  assumes "sound_proc p" "p g = Closed"
  shows "provable g"
  using assms unfolding sound_proc_def by blast

lemma sound_g_auto_processor: "sound_proc (g_auto_processor \<Sigma> axs k)"
  unfolding sound_proc_def
proof (intro allI conjI impI)
  fix g
  let ?U = "auto_universe k g"
  let ?ns = "remdups (concat (map tm_name_list ?U))"
  let ?r = "foldr max (map tm_size ?U) 0"
  have eq: "g_auto_processor \<Sigma> axs k g = g_processor \<Sigma> axs ?ns ?r (fst g) ?U g"
    by (simp add: g_auto_processor_def Let_def)
  assume "g_auto_processor \<Sigma> axs k g = Closed"
  then have "g_processor \<Sigma> axs ?ns ?r (fst g) ?U g = Closed" using eq by simp
  from sound_proc_Closed[OF sound_g_processor this] show "provable g" .
next
  fix g gs
  assume "g_auto_processor \<Sigma> axs k g = Subgoals gs" "\<forall>g'\<in>set gs. provable g'"
  then show "provable g"
    by (simp add: g_auto_processor_def Let_def g_processor_def split: if_splits)
qed

text \<open>The full stage is complete in the limit.\<close>

theorem g_full_complete:
  "provable g \<longleftrightarrow> (\<exists>ns r. g_full_processor \<Sigma> axs ns r g = Closed)"
proof
  assume "\<exists>ns r. g_full_processor \<Sigma> axs ns r g = Closed"
  then obtain ns r where "g_full_processor \<Sigma> axs ns r g = Closed" by blast
  then have "g_processor \<Sigma> axs ns r (enum_tm ns \<Sigma> r) (enum_tm ns \<Sigma> r) g = Closed"
    by (simp add: g_full_processor_def)
  from sound_proc_Closed[OF sound_g_processor this] show "provable g" .
next
  assume "provable g"
  then obtain \<Gamma> where sub: "\<Gamma> \<subseteq> set (fst g)" and d: "derivable \<Gamma> (snd g)"
    by (auto simp: provable_iff)
  from d obtain N r where fN: "finite N" and b: "bderiv N r (\<Gamma>, snd g)"
    using derivable_iff_bderiv by blast
  obtain ns where ns: "set ns = N" using finite_list[OF fN] by blast
  have gd: "gderiv (Tm_wt (set ns) \<Sigma> r) (Tm_wt (set ns) \<Sigma> r) (\<Gamma>, snd g)"
    using b ns by (simp add: bderiv_iff_gderiv)
  have "set (enum_tm ns \<Sigma> r) \<inter> Tm_wt (set ns) \<Sigma> r = Tm_wt (set ns) \<Sigma> r"
    by (simp add: set_enum_tm)
  then have "gflood_decide \<Sigma> axs ns r (enum_tm ns \<Sigma> r) (enum_tm ns \<Sigma> r) (\<Gamma>, snd g)"
    using gd gflood_decide_iff_gderiv by simp
  then have mem: "(\<Gamma>, snd g) \<in> set (g_flood_result \<Sigma> axs ns r (enum_tm ns \<Sigma> r) (enum_tm ns \<Sigma> r))"
    by (simp add: gflood_decide_eq_result)
  have "list_ex (\<lambda>q. snd q = snd g \<and> (\<forall>h\<in>fst q. h \<in> set (fst g)))
                (g_flood_result \<Sigma> axs ns r (enum_tm ns \<Sigma> r) (enum_tm ns \<Sigma> r))"
    using mem sub by (auto simp: list_ex_iff intro!: bexI[of _ "(\<Gamma>, snd g)"])
  then show "\<exists>ns r. g_full_processor \<Sigma> axs ns r g = Closed"
    by (auto simp: g_full_processor_def g_processor_def intro!: exI[of _ ns] exI[of _ r])
qed

text \<open>
  The staged prover is sound, and, because of the last stage, every provable goal is proved by
  some choice of the bounds.
\<close>

theorem g_prove_sound: "g_prove \<Sigma> axs k ns r n g \<Longrightarrow> provable g"
proof -
  assume h: "g_prove \<Sigma> axs k ns r n g"
  have procs: "\<forall>p\<in>set (default_procs \<Sigma> @ [g_auto_processor \<Sigma> axs k]). sound_proc p"
    using sound_default_procs sound_g_auto_processor by auto
  from h show "provable g"
  proof (unfold g_prove_def, elim disjE)
    assume "waterfall n (default_procs \<Sigma> @ [g_auto_processor \<Sigma> axs k]) g = []"
    then have "\<forall>g'\<in>set (waterfall n (default_procs \<Sigma> @ [g_auto_processor \<Sigma> axs k]) g). provable g'"
      by simp
    from waterfall_sound[OF procs this] show ?thesis .
  next
    assume "g_full_processor \<Sigma> axs ns r g = Closed"
    then show ?thesis using g_full_complete by blast
  qed
qed

theorem g_prove_complete_in_limit:
  "provable g \<longleftrightarrow> (\<exists>k ns r n. g_prove \<Sigma> axs k ns r n g)"
proof
  assume "provable g"
  then obtain ns r where "g_full_processor \<Sigma> axs ns r g = Closed"
    using g_full_complete by blast
  then show "\<exists>k ns r n. g_prove \<Sigma> axs k ns r n g" by (auto simp: g_prove_def)
next
  assume "\<exists>k ns r n. g_prove \<Sigma> axs k ns r n g"
  then show "provable g" using g_prove_sound by blast
qed

end

end
