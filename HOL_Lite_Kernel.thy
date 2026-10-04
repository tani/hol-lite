theory HOL_Lite_Kernel
  imports Main
begin

text \<open>
  Kernel for the Boyer-Moore waterfall (cf. "The Boyer-Moore Waterfall Model Revisited",
  arXiv:1808.03810): terms of a small natural-number shell, clauses (disjunctions of
  possibly negated equations), their semantics and validity, substitution, replacement,
  and the notion of a sound process outcome.
\<close>

section \<open>Terms, clauses and semantics\<close>

datatype trm = TV nat | TZ | TS trm | TP trm trm | TM trm trm

type_synonym lit = "bool \<times> trm \<times> trm"   \<comment> \<open>(polarity, lhs, rhs): lhs = rhs if True, lhs \<noteq> rhs if False\<close>
type_synonym clause = "lit list"           \<comment> \<open>disjunction of literals\<close>

primrec ev :: "(nat \<Rightarrow> nat) \<Rightarrow> trm \<Rightarrow> nat" where
  "ev e (TV x) = e x"
| "ev e TZ = 0"
| "ev e (TS t) = Suc (ev e t)"
| "ev e (TP a b) = ev e a + ev e b"
| "ev e (TM a b) = ev e a * ev e b"

fun lit_holds :: "(nat \<Rightarrow> nat) \<Rightarrow> lit \<Rightarrow> bool" where
  "lit_holds e (s, a, b) = ((ev e a = ev e b) = s)"

definition holds :: "(nat \<Rightarrow> nat) \<Rightarrow> clause \<Rightarrow> bool" where
  "holds e cl = (\<exists>l\<in>set cl. lit_holds e l)"

definition valid :: "clause \<Rightarrow> bool" where
  "valid cl = (\<forall>e. holds e cl)"

lemma holds_Nil [simp]: "holds e [] = False"
  by (simp add: holds_def)

lemma holds_Cons [simp]: "holds e (l # cl) = (lit_holds e l \<or> holds e cl)"
  by (simp add: holds_def)

lemma holds_append [simp]: "holds e (c1 @ c2) = (holds e c1 \<or> holds e c2)"
  by (auto simp: holds_def)

lemma holds_mono: "set c1 \<subseteq> set c2 \<Longrightarrow> holds e c1 \<Longrightarrow> holds e c2"
  by (auto simp: holds_def)

lemma holds_mem: "l \<in> set cl \<Longrightarrow> lit_holds e l \<Longrightarrow> holds e cl"
  by (auto simp: holds_def)

lemma lit_obtain: obtains s a b where "(l :: lit) = (s, a, b)"
  by (metis prod_cases3)

section \<open>Variables, substitution, replacement\<close>

primrec tvars :: "trm \<Rightarrow> nat list" where
  "tvars (TV x) = [x]"
| "tvars TZ = []"
| "tvars (TS t) = tvars t"
| "tvars (TP a b) = tvars a @ tvars b"
| "tvars (TM a b) = tvars a @ tvars b"

fun lvars :: "lit \<Rightarrow> nat list" where
  "lvars (s, a, b) = tvars a @ tvars b"

primrec cvars :: "clause \<Rightarrow> nat list" where
  "cvars [] = []"
| "cvars (l # cl) = lvars l @ cvars cl"

lemma lvars_cvars: "l \<in> set cl \<Longrightarrow> v \<in> set (lvars l) \<Longrightarrow> v \<in> set (cvars cl)"
  by (induction cl) auto

lemma ev_cong: "(\<forall>v. v \<in> set (tvars t) \<longrightarrow> e1 v = e2 v) \<Longrightarrow> ev e1 t = ev e2 t"
  by (induction t) auto

lemma lit_holds_cong:
  assumes "\<forall>v. v \<in> set (lvars l) \<longrightarrow> e1 v = e2 v"
  shows "lit_holds e1 l = lit_holds e2 l"
proof -
  obtain s a b where l: "l = (s, a, b)" by (rule lit_obtain)
  have "ev e1 a = ev e2 a" "ev e1 b = ev e2 b"
    using assms l by (auto intro: ev_cong)
  then show ?thesis using l by simp
qed

lemma holds_cong:
  assumes "\<forall>v. v \<in> set (cvars cl) \<longrightarrow> e1 v = e2 v"
  shows "holds e1 cl = holds e2 cl"
proof -
  have "\<And>l. l \<in> set cl \<Longrightarrow> lit_holds e1 l = lit_holds e2 l"
    using assms lvars_cvars by (blast intro: lit_holds_cong)
  then show ?thesis by (auto simp: holds_def)
qed

definition fresh :: "clause \<Rightarrow> nat" where
  "fresh cl = Suc (foldr max (cvars cl) 0)"

lemma mem_le_foldr: "x \<in> set vs \<Longrightarrow> x \<le> foldr max vs 0"
  by (induction vs) (auto simp: le_max_iff_disj)

lemma fresh_notin: "fresh cl \<notin> set (cvars cl)"
  by (auto simp: fresh_def dest: mem_le_foldr)

primrec tsubst :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm" where
  "tsubst x r (TV y) = (if y = x then r else TV y)"
| "tsubst x r TZ = TZ"
| "tsubst x r (TS t) = TS (tsubst x r t)"
| "tsubst x r (TP a b) = TP (tsubst x r a) (tsubst x r b)"
| "tsubst x r (TM a b) = TM (tsubst x r a) (tsubst x r b)"

lemma ev_tsubst: "ev e (tsubst x r t) = ev (e(x := ev e r)) t"
  by (induction t) auto

fun lsubst :: "nat \<Rightarrow> trm \<Rightarrow> lit \<Rightarrow> lit" where
  "lsubst x r (s, a, b) = (s, tsubst x r a, tsubst x r b)"

definition csubst :: "nat \<Rightarrow> trm \<Rightarrow> clause \<Rightarrow> clause" where
  "csubst x r cl = map (lsubst x r) cl"

lemma lit_holds_lsubst: "lit_holds e (lsubst x r l) = lit_holds (e(x := ev e r)) l"
proof -
  obtain s a b where "l = (s, a, b)" by (rule lit_obtain)
  then show ?thesis by (simp add: ev_tsubst)
qed

lemma holds_csubst: "holds e (csubst x r cl) = holds (e(x := ev e r)) cl"
  by (auto simp: holds_def csubst_def lit_holds_lsubst)

text \<open>Replacement of a term @{text a} by @{text b} (used by cross-fertilization and generalization).\<close>

primrec trep :: "trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm" where
  "trep a b (TV y) = (if TV y = a then b else TV y)"
| "trep a b TZ = (if TZ = a then b else TZ)"
| "trep a b (TS t) = (if TS t = a then b else TS (trep a b t))"
| "trep a b (TP u v) = (if TP u v = a then b else TP (trep a b u) (trep a b v))"
| "trep a b (TM u v) = (if TM u v = a then b else TM (trep a b u) (trep a b v))"

fun lrep :: "trm \<Rightarrow> trm \<Rightarrow> lit \<Rightarrow> lit" where
  "lrep a b (s, u, v) = (s, trep a b u, trep a b v)"

definition crep :: "trm \<Rightarrow> trm \<Rightarrow> clause \<Rightarrow> clause" where
  "crep a b cl = map (lrep a b) cl"

lemma ev_trep_eq: "ev e a = ev e b \<Longrightarrow> ev e (trep a b t) = ev e t"
  by (induction t) auto

lemma lit_holds_lrep_eq:
  "ev e a = ev e b \<Longrightarrow> lit_holds e (lrep a b l) = lit_holds e l"
proof -
  assume h: "ev e a = ev e b"
  obtain s u v where "l = (s, u, v)" by (rule lit_obtain)
  then show ?thesis by (simp add: ev_trep_eq[OF h])
qed

lemma ev_trep_var:
  "x \<notin> set (tvars u) \<Longrightarrow> ev (e(x := ev e t)) (trep t (TV x) u) = ev e u"
  by (induction u) auto

lemma lit_holds_lrep_var:
  "x \<notin> set (lvars l) \<Longrightarrow> lit_holds (e(x := ev e t)) (lrep t (TV x) l) = lit_holds e l"
proof -
  assume h: "x \<notin> set (lvars l)"
  obtain s u v where l: "l = (s, u, v)" by (rule lit_obtain)
  then show ?thesis using h by (simp add: ev_trep_var)
qed

lemma holds_crep_var:
  assumes "x \<notin> set (cvars cl)"
  shows "holds (e(x := ev e t)) (crep t (TV x) cl) = holds e cl"
proof -
  have "\<And>l. l \<in> set cl \<Longrightarrow> x \<notin> set (lvars l)"
    using assms lvars_cvars by blast
  then show ?thesis
    by (auto simp: holds_def crep_def lit_holds_lrep_var)
qed

section \<open>Outcomes of processes and their soundness\<close>

datatype outcome = Proved | Refuted | Subgoals "clause list" | Pass

fun sound_out :: "clause \<Rightarrow> outcome \<Rightarrow> bool" where
  "sound_out cl Proved = valid cl"
| "sound_out cl Refuted = (\<not> valid cl)"
| "sound_out cl (Subgoals cs) = ((\<forall>c\<in>set cs. valid c) \<longrightarrow> valid cl)"
| "sound_out cl Pass = True"

end
