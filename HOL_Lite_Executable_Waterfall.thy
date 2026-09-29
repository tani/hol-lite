theory HOL_Lite_Executable_Waterfall
  imports HOL_Lite_Executable_Core
begin

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
