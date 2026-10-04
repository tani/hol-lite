theory HOL_Lite_Waterfall
  imports HOL_Lite_Kernel
begin

text \<open>
  The waterfall: tautology check, counterexample check, substitution, simplification,
  equality (cross-fertilization) and generalization, each proved sound against the
  kernel semantics; induction on the pool; and the fuel-bounded prover with its
  soundness theorem.
\<close>

section \<open>Process: tautology check\<close>

fun taut_lit :: "clause \<Rightarrow> lit \<Rightarrow> bool" where
  "taut_lit cl (s, a, b) = (s \<and> (a = b \<or> (False, a, b) \<in> set cl))"

definition is_taut :: "clause \<Rightarrow> bool" where
  "is_taut cl = list_ex (taut_lit cl) cl"

lemma taut_holds: "is_taut cl \<Longrightarrow> holds e cl"
proof -
  assume "is_taut cl"
  then obtain l where l: "l \<in> set cl" "taut_lit cl l"
    by (auto simp: is_taut_def list_ex_iff)
  obtain s a b where lab: "l = (s, a, b)" by (rule lit_obtain)
  with l have s: "s" and ab: "a = b \<or> (False, a, b) \<in> set cl" by auto
  show ?thesis
  proof (cases "a = b")
    case True
    with s lab l show ?thesis by (auto intro: holds_mem)
  next
    case False
    with ab have neg: "(False, a, b) \<in> set cl" by simp
    show ?thesis
    proof (cases "ev e a = ev e b")
      case True
      with s lab l show ?thesis by (auto intro: holds_mem)
    next
      case False
      with neg show ?thesis by (auto intro: holds_mem)
    qed
  qed
qed

definition taut_proc :: "clause \<Rightarrow> outcome" where
  "taut_proc cl = (if is_taut cl then Proved else Pass)"

lemma taut_proc_sound: "sound_out cl (taut_proc cl)"
  by (simp add: taut_proc_def valid_def taut_holds)

section \<open>Process: counterexample check\<close>

fun envs :: "nat list \<Rightarrow> (nat \<Rightarrow> nat) list" where
  "envs [] = [\<lambda>_. 0]"
| "envs (v # vs) = concat (map (\<lambda>e. map (\<lambda>k. e(v := k)) [0, 1, 2]) (envs vs))"

definition refuted :: "clause \<Rightarrow> bool" where
  "refuted cl = list_ex (\<lambda>e. \<not> holds e cl) (envs (cvars cl))"

definition counter_proc :: "clause \<Rightarrow> outcome" where
  "counter_proc cl = (if refuted cl then Refuted else Pass)"

lemma refuted_not_valid: "refuted cl \<Longrightarrow> \<not> valid cl"
  by (auto simp: refuted_def list_ex_iff valid_def)

lemma counter_proc_sound: "sound_out cl (counter_proc cl)"
  by (simp add: counter_proc_def refuted_not_valid)

section \<open>Literal-driven steps (substitution and equality)\<close>

definition good_step :: "(lit \<Rightarrow> clause \<Rightarrow> clause list) \<Rightarrow> bool" where
  "good_step st = (\<forall>l n cl. l \<in> set cl \<longrightarrow> n \<in> set (st l cl) \<longrightarrow> valid n \<longrightarrow> valid cl)"

definition first_step :: "(lit \<Rightarrow> clause \<Rightarrow> clause list) \<Rightarrow> clause \<Rightarrow> outcome" where
  "first_step st cl = (case concat (map (\<lambda>l. st l cl) cl) of [] \<Rightarrow> Pass | n # _ \<Rightarrow> Subgoals [n])"

lemma first_step_sound:
  assumes "good_step st"
  shows "sound_out cl (first_step st cl)"
proof (cases "concat (map (\<lambda>l. st l cl) cl)")
  case Nil
  then show ?thesis by (simp add: first_step_def)
next
  case (Cons n ns)
  then have "n \<in> set (concat (map (\<lambda>l. st l cl) cl))" by simp
  then obtain l where l: "l \<in> set cl" "n \<in> set (st l cl)" by auto
  have "valid n \<longrightarrow> valid cl" using assms l unfolding good_step_def by blast
  then show ?thesis using Cons by (simp add: first_step_def)
qed

subsection \<open>Substitution: eliminate a negated equality x \<noteq> t\<close>

fun subst_step :: "lit \<Rightarrow> clause \<Rightarrow> clause list" where
  "subst_step (s, a, t) cl =
     (case a of
        TV x \<Rightarrow> if \<not> s \<and> x \<notin> set (tvars t)
                then [csubst x t (remove1 (s, a, t) cl)] else []
      | _ \<Rightarrow> [])"

lemma good_subst_step: "good_step subst_step"
  unfolding good_step_def
proof (intro allI impI)
  fix l n cl
  assume lcl: "l \<in> set cl" and n: "n \<in> set (subst_step l cl)" and vn: "valid n"
  obtain s a t where l: "l = (s, a, t)" by (rule lit_obtain)
  show "valid cl"
  proof (cases a)
    case (TV x)
    with n l have s: "\<not> s" and nn: "n = csubst x t (remove1 (s, a, t) cl)"
      by (auto split: if_splits)
    show ?thesis
      unfolding valid_def
    proof
      fix e
      have hn: "holds (e(x := ev e t)) (remove1 (s, a, t) cl)"
        using vn nn unfolding valid_def by (auto simp: holds_csubst)
      show "holds e cl"
      proof (cases "e x = ev e t")
        case True
        then have "e(x := ev e t) = e" by (simp add: fun_upd_idem)
        with hn have "holds e (remove1 (s, a, t) cl)" by simp
        then show ?thesis by (rule holds_mono[OF set_remove1_subset])
      next
        case False
        with TV s have "lit_holds e (s, a, t)" by simp
        with lcl l show ?thesis by (auto intro: holds_mem)
      qed
    qed
  next
    case TZ with n l show ?thesis by simp
  next
    case TS with n l show ?thesis by simp
  next
    case TP with n l show ?thesis by simp
  next
    case TM with n l show ?thesis by simp
  qed
qed

definition subst_proc :: "clause \<Rightarrow> outcome" where
  "subst_proc = first_step subst_step"

lemma subst_proc_sound: "sound_out cl (subst_proc cl)"
  unfolding subst_proc_def by (rule first_step_sound[OF good_subst_step])

subsection \<open>Equality (cross-fertilization): use a hypothesis a \<noteq> b to replace a by b\<close>

primrec is_tmpl :: "trm \<Rightarrow> bool" where   \<comment> \<open>explicit value templates\<close>
  "is_tmpl (TV x) = True"
| "is_tmpl TZ = True"
| "is_tmpl (TS t) = is_tmpl t"
| "is_tmpl (TP a b) = False"
| "is_tmpl (TM a b) = False"

fun eq_step :: "lit \<Rightarrow> clause \<Rightarrow> clause list" where
  "eq_step (s, a, b) cl =
     (if \<not> s \<and> a \<noteq> b \<and> \<not> is_tmpl a
         \<and> map (lrep a b) (remove1 (s, a, b) cl) \<noteq> remove1 (s, a, b) cl
      then [(s, a, b) # map (lrep a b) (remove1 (s, a, b) cl)] else [])"

lemma good_eq_step: "good_step eq_step"
  unfolding good_step_def
proof (intro allI impI)
  fix l n cl
  assume lcl: "l \<in> set cl" and n: "n \<in> set (eq_step l cl)" and vn: "valid n"
  obtain s a b where l: "l = (s, a, b)" by (rule lit_obtain)
  from n l have s: "\<not> s" and nn: "n = (s, a, b) # map (lrep a b) (remove1 (s, a, b) cl)"
    by (auto split: if_splits)
  show "valid cl"
    unfolding valid_def
  proof
    fix e
    have hn: "holds e n" using vn unfolding valid_def by blast
    show "holds e cl"
    proof (cases "ev e a = ev e b")
      case True
      then have "\<not> lit_holds e (s, a, b)" using s by simp
      with hn nn have "holds e (map (lrep a b) (remove1 (s, a, b) cl))" by simp
      then obtain l' where l': "l' \<in> set (remove1 (s, a, b) cl)" "lit_holds e (lrep a b l')"
        by (auto simp: holds_def)
      from l'(2) True have "lit_holds e l'" by (simp add: lit_holds_lrep_eq)
      moreover have "l' \<in> set cl" using l'(1) set_remove1_subset by blast
      ultimately show ?thesis by (rule holds_mem[rotated])
    next
      case False
      with s have "lit_holds e (s, a, b)" by simp
      with lcl l show ?thesis by (auto intro: holds_mem)
    qed
  qed
qed

definition equal_proc :: "clause \<Rightarrow> outcome" where
  "equal_proc = first_step eq_step"

lemma equal_proc_sound: "sound_out cl (equal_proc cl)"
  unfolding equal_proc_def by (rule first_step_sound[OF good_eq_step])

section \<open>Process: simplification\<close>

text \<open>Rewrite rules: the recursive definitions of addition and multiplication;
  then equations between successor/zero terms are decomposed.\<close>

fun rw :: "trm \<Rightarrow> trm" where
  "rw (TP TZ y) = y"
| "rw (TP (TS x) y) = TS (TP x y)"
| "rw (TM TZ y) = TZ"
| "rw (TM (TS x) y) = TP y (TM x y)"
| "rw t = t"

lemma ev_rw: "ev e (rw t) = ev e t"
  by (induction t rule: rw.induct) auto

primrec simp_t :: "trm \<Rightarrow> trm" where
  "simp_t (TV x) = TV x"
| "simp_t TZ = TZ"
| "simp_t (TS t) = TS (simp_t t)"
| "simp_t (TP a b) = rw (TP (simp_t a) (simp_t b))"
| "simp_t (TM a b) = rw (TM (simp_t a) (simp_t b))"

lemma ev_simp_t: "ev e (simp_t t) = ev e t"
  by (induction t) (simp_all add: ev_rw)

primrec simp_n :: "nat \<Rightarrow> trm \<Rightarrow> trm" where
  "simp_n 0 t = t"
| "simp_n (Suc n) t = simp_n n (simp_t t)"

lemma ev_simp_n: "ev e (simp_n n t) = ev e t"
  by (induction n arbitrary: t) (simp_all add: ev_simp_t)

fun simp_eq :: "bool \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> lit list" where
  "simp_eq s (TS a) (TS b) = simp_eq s a b"
| "simp_eq s TZ TZ = (if s then [(True, TZ, TZ)] else [])"
| "simp_eq s (TS a) TZ = (if s then [] else [(True, TZ, TZ)])"
| "simp_eq s TZ (TS b) = (if s then [] else [(True, TZ, TZ)])"
| "simp_eq s a b = (if a = b then (if s then [(True, TZ, TZ)] else []) else [(s, a, b)])"

lemma holds_simp_eq: "holds e (simp_eq s a b) = lit_holds e (s, a, b)"
  by (induction s a b rule: simp_eq.induct) auto

fun simp_lit :: "lit \<Rightarrow> clause" where
  "simp_lit (s, a, b) = simp_eq s (simp_n 8 a) (simp_n 8 b)"

lemma holds_simp_lit: "holds e (simp_lit l) = lit_holds e l"
proof -
  obtain s a b where "l = (s, a, b)" by (rule lit_obtain)
  then show ?thesis by (simp add: holds_simp_eq ev_simp_n)
qed

primrec simp_clause :: "clause \<Rightarrow> clause" where
  "simp_clause [] = []"
| "simp_clause (l # cl) = simp_lit l @ simp_clause cl"

lemma holds_simp_clause: "holds e (simp_clause cl) = holds e cl"
  by (induction cl) (simp_all add: holds_simp_lit)

definition simp_proc :: "clause \<Rightarrow> outcome" where
  "simp_proc cl = (let cl' = simp_clause cl in if cl' = cl then Pass else Subgoals [cl'])"

lemma simp_proc_sound: "sound_out cl (simp_proc cl)"
  by (auto simp: simp_proc_def Let_def valid_def holds_simp_clause)

section \<open>Process: generalization\<close>

fun subs :: "trm \<Rightarrow> trm list" where
  "subs (TV x) = [TV x]"
| "subs TZ = [TZ]"
| "subs (TS t) = TS t # subs t"
| "subs (TP a b) = TP a b # subs a @ subs b"
| "subs (TM a b) = TM a b # subs a @ subs b"

fun lsubs :: "lit \<Rightarrow> trm list" where
  "lsubs (s, a, b) = subs a @ subs b"

definition csubs :: "clause \<Rightarrow> trm list" where
  "csubs cl = concat (map lsubs cl)"

text \<open>Candidates: non-template subterms occurring at least twice in the clause.\<close>

definition gen_cands :: "clause \<Rightarrow> trm list" where
  "gen_cands cl = [t. t \<leftarrow> csubs cl, \<not> is_tmpl t, 2 \<le> length (filter (\<lambda>u. u = t) (csubs cl))]"

lemma gen_valid:
  "valid (crep t (TV (fresh cl)) cl) \<Longrightarrow> valid cl"
  unfolding valid_def
proof
  fix e
  assume "\<forall>e. holds e (crep t (TV (fresh cl)) cl)"
  then have "holds (e(fresh cl := ev e t)) (crep t (TV (fresh cl)) cl)" by blast
  then show "holds e cl" by (simp add: holds_crep_var[OF fresh_notin])
qed

definition gen_proc :: "clause \<Rightarrow> outcome" where
  "gen_proc cl =
     (case gen_cands cl of
        [] \<Rightarrow> Pass
      | t # _ \<Rightarrow>
          (let cl' = crep t (TV (fresh cl)) cl
           in if refuted cl' then Pass else Subgoals [cl']))"

lemma gen_proc_sound: "sound_out cl (gen_proc cl)"
proof (cases "gen_cands cl")
  case Nil
  then show ?thesis by (simp add: gen_proc_def)
next
  case (Cons t ts)
  have key: "valid (crep t (TV (fresh cl)) cl) \<longrightarrow> valid cl"
    using gen_valid by blast
  show ?thesis using Cons key by (auto simp: gen_proc_def Let_def)
qed

section \<open>The waterfall\<close>

datatype process = P_Taut | P_Counter | P_Subst | P_Simp | P_Equal | P_Gen

fun run :: "process \<Rightarrow> clause \<Rightarrow> outcome" where
  "run P_Taut cl = taut_proc cl"
| "run P_Counter cl = counter_proc cl"
| "run P_Subst cl = subst_proc cl"
| "run P_Simp cl = simp_proc cl"
| "run P_Equal cl = equal_proc cl"
| "run P_Gen cl = gen_proc cl"

lemma run_sound: "sound_out cl (run p cl)"
  by (cases p)
     (simp_all add: taut_proc_sound counter_proc_sound subst_proc_sound
                    simp_proc_sound equal_proc_sound gen_proc_sound)

text \<open>A waterfall is an ordered list of processes; a clause flows down until a
  process does something with it.\<close>

fun pipeline :: "process list \<Rightarrow> clause \<Rightarrow> outcome" where
  "pipeline [] cl = Pass"
| "pipeline (p # ps) cl = (case run p cl of Pass \<Rightarrow> pipeline ps cl | o \<Rightarrow> o)"

lemma pipeline_sound: "sound_out cl (pipeline ps cl)"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have "sound_out cl (run p cl)" by (rule run_sound)
  then show ?case using Cons.IH by (cases "run p cl") auto
qed

definition default_waterfall :: "process list" where
  "default_waterfall = [P_Taut, P_Subst, P_Simp, P_Equal, P_Gen]"

section \<open>Induction\<close>

text \<open>Induction on a variable x of the clause: base case x := 0, and for every
  literal l of the clause one step clause  c[x := S y] \<or> \<not> l[x := y]  with y fresh.\<close>

fun neg :: "lit \<Rightarrow> lit" where
  "neg (s, a, b) = (\<not> s, a, b)"

lemma lit_holds_neg: "lit_holds e (neg l) = (\<not> lit_holds e l)"
proof -
  obtain s a b where "l = (s, a, b)" by (rule lit_obtain)
  then show ?thesis by auto
qed

definition step_clause :: "nat \<Rightarrow> clause \<Rightarrow> lit \<Rightarrow> clause" where
  "step_clause x cl l =
     csubst x (TS (TV (fresh cl))) cl @ [neg (lsubst x (TV (fresh cl)) l)]"

definition ind_goals :: "nat \<Rightarrow> clause \<Rightarrow> clause list" where
  "ind_goals x cl = csubst x TZ cl # map (step_clause x cl) cl"

lemma ind_sound:
  assumes xn: "x \<in> set (cvars cl)" and goals: "\<forall>c\<in>set (ind_goals x cl). valid c"
  shows "valid cl"
proof -
  let ?y = "fresh cl"
  have hy: "?y \<notin> set (cvars cl)" by (rule fresh_notin)
  have base: "valid (csubst x TZ cl)" using goals by (simp add: ind_goals_def)
  have step: "\<And>l. l \<in> set cl \<Longrightarrow> valid (step_clause x cl l)"
    using goals by (auto simp: ind_goals_def)
  have main: "\<And>e n. holds (e(x := n)) cl"
  proof -
    fix e n
    show "holds (e(x := n)) cl"
    proof (induction n)
      case 0
      have "holds e (csubst x TZ cl)" using base unfolding valid_def by blast
      then show ?case by (simp add: holds_csubst)
    next
      case (Suc n)
      from Suc.IH obtain l where l: "l \<in> set cl" "lit_holds (e(x := n)) l"
        by (auto simp: holds_def)
      let ?e' = "(e(x := n))(?y := n)"
      have hs: "holds ?e' (step_clause x cl l)"
        using step[OF l(1)] unfolding valid_def by blast
      have vl: "\<And>v. v \<in> set (lvars l) \<Longrightarrow> v \<noteq> ?y"
        using hy lvars_cvars[OF l(1)] by blast
      have c1: "lit_holds (?e'(x := n)) l = lit_holds (e(x := n)) l"
        by (rule lit_holds_cong) (auto simp: fun_upd_apply dest: vl)
      have negfalse: "\<not> lit_holds ?e' (neg (lsubst x (TV ?y) l))"
        using l(2) c1 by (simp add: lit_holds_neg lit_holds_lsubst)
      have hc: "holds ?e' (csubst x (TS (TV ?y)) cl)"
        using hs negfalse by (auto simp: step_clause_def)
      have c2: "holds (?e'(x := Suc n)) cl = holds (e(x := Suc n)) cl"
        by (rule holds_cong) (auto simp: fun_upd_apply dest: hy)
      show ?case using hc c2 by (simp add: holds_csubst)
    qed
  qed
  show ?thesis
    unfolding valid_def
  proof
    fix e
    have "holds (e(x := e x)) cl" by (rule main)
    then show "holds e cl" by simp
  qed
qed

text \<open>Heuristic choice of induction variable: variables in recursive (first-argument)
  positions of + and *, otherwise any variable.  Soundness does not depend on it.\<close>

fun rvs :: "trm \<Rightarrow> nat list" where
  "rvs (TV x) = []"
| "rvs TZ = []"
| "rvs (TS t) = rvs t"
| "rvs (TP a b) = (case a of TV x \<Rightarrow> [x] | _ \<Rightarrow> []) @ rvs a @ rvs b"
| "rvs (TM a b) = (case a of TV x \<Rightarrow> [x] | _ \<Rightarrow> []) @ rvs a @ rvs b"

fun lrvs :: "lit \<Rightarrow> nat list" where
  "lrvs (s, a, b) = rvs a @ rvs b"

definition ind_var :: "clause \<Rightarrow> nat option" where
  "ind_var cl =
     (case concat (map lrvs cl) @ cvars cl of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x)"

definition induct :: "clause \<Rightarrow> clause list option" where
  "induct cl = (case ind_var cl of
                  None \<Rightarrow> None
                | Some x \<Rightarrow> if x \<in> set (cvars cl) then Some (ind_goals x cl) else None)"

lemma induct_sound:
  assumes "induct cl = Some cs" and "\<forall>c\<in>set cs. valid c"
  shows "valid cl"
proof -
  obtain x where "ind_var cl = Some x"
    using assms(1) by (cases "ind_var cl") (auto simp: induct_def)
  with assms(1) have "x \<in> set (cvars cl)" "cs = ind_goals x cl"
    by (auto simp: induct_def split: if_splits)
  with assms(2) show ?thesis by (auto intro: ind_sound)
qed

section \<open>The prover and its soundness theorem\<close>

text \<open>Fuel-bounded: every call of the waterfall (including the recursive pours after
  induction) consumes fuel, so the function is total.  Clauses passing through the whole
  waterfall without being proved form the pool and are handed to induction.\<close>

primrec prove :: "process list \<Rightarrow> nat \<Rightarrow> clause \<Rightarrow> bool" where
  "prove ws 0 cl = False"
| "prove ws (Suc n) cl =
     (case pipeline ws cl of
        Proved \<Rightarrow> True
      | Refuted \<Rightarrow> False
      | Subgoals cs \<Rightarrow> (\<forall>c\<in>set cs. prove ws n c)
      | Pass \<Rightarrow> (case induct cl of
                    None \<Rightarrow> False
                  | Some cs \<Rightarrow> (\<forall>c\<in>set cs. prove ws n c)))"

theorem prove_sound: "prove ws n cl \<Longrightarrow> valid cl"
proof (induction n arbitrary: cl)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have so: "sound_out cl (pipeline ws cl)" by (rule pipeline_sound)
  show ?case
  proof (cases "pipeline ws cl")
    case Proved
    with so show ?thesis by simp
  next
    case Refuted
    with Suc.prems show ?thesis by simp
  next
    case (Subgoals cs)
    with Suc.prems have "\<forall>c\<in>set cs. prove ws n c" by simp
    then have "\<forall>c\<in>set cs. valid c" using Suc.IH by blast
    with so Subgoals show ?thesis by simp
  next
    case Pass
    show ?thesis
    proof (cases "induct cl")
      case None
      with Suc.prems Pass show ?thesis by simp
    next
      case (Some cs)
      with Suc.prems Pass have "\<forall>c\<in>set cs. prove ws n c" by simp
      then have "\<forall>c\<in>set cs. valid c" using Suc.IH by blast
      with Some show ?thesis by (rule induct_sound)
    qed
  qed
qed

corollary valid_by_waterfall:
  "prove default_waterfall n cl \<Longrightarrow> valid cl"
  by (rule prove_sound)

section \<open>Examples\<close>

text \<open>x + 0 = x\<close>
lemma plus_zero_right: "valid [(True, TP (TV 0) TZ, TV 0)]"
  by (rule valid_by_waterfall[of 10]) (eval)

text \<open>(x + y) + z = x + (y + z)\<close>
lemma plus_assoc:
  "valid [(True, TP (TP (TV 0) (TV 1)) (TV 2), TP (TV 0) (TP (TV 1) (TV 2)))]"
  by (rule valid_by_waterfall[of 10]) (eval)

end
