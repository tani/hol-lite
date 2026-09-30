theory HOL_Lite_Guided_Examples
  imports HOL_Lite_Guided_Flood HOL_Lite_Bounded_Examples
begin

section \<open>Guided flood on goals of realistic size\<close>

text \<open>
  An equation between two boolean variables already has size 12, so the full-region flood of
  @{text HOL_Lite_Flood} (which enumerates every term up to size @{text r}) cannot reach such
  goals.  The guided flood only needs the universe of terms the derivation passes through.
  The names and the size bound are used to check well-typedness and to query the axiom oracle,
  not to enumerate.
\<close>

definition ns5 :: "name list" where
  "ns5 = [''fun'', ''bool'', ''='', ''p'', ''q'']"

definition tp :: tm where "tp = Fv ''p'' boolT"
definition tq :: tm where "tq = Fv ''q'' boolT"
definition eqc :: tm where "eqc = Cst ''='' (funT boolT (funT boolT boolT))"

definition pq :: tm where "pq = mk_eq boolT tp tq"
definition qp :: tm where "qp = mk_eq boolT tq tp"
definition pp :: tm where "pp = mk_eq boolT tp tp"

text \<open>Modus ponens for an equation: @{text "{p = q, p} \<turnstile> q"} needs only three terms.\<close>

definition U_mp :: "tm list" where "U_mp = [tp, tq, pq]"

lemma mp_found:
  "gflood_decide base_hsig empty_axs ns5 40 U_mp ({pq, tp}, tq)"
  by eval

text \<open>
  Symmetry @{text "{p = q} \<turnstile> q = p"} goes through the equations
  @{text "(=) = (=)"}, @{text "(=) p = (=) q"} and @{text "(p = p) = (q = p)"}.
\<close>

definition e1 :: tm where "e1 = mk_eq (funT boolT (funT boolT boolT)) eqc eqc"
definition e2 :: tm where "e2 = mk_eq (funT boolT boolT) (App eqc tp) (App eqc tq)"
definition e3 :: tm where "e3 = mk_eq boolT (App (App eqc tp) tp) (App (App eqc tq) tp)"

definition U_sym :: "tm list" where "U_sym = [tp, tq, pq, qp, pp, e1, e2, e3]"

lemma sym_found:
  "gflood_decide base_hsig empty_axs ns5 40 U_sym ({pq}, qp)"
  by eval

text \<open>
  Completeness holds relative to the universe, not beyond it: with the intermediate equation
  @{text e3} left out of the universe the same goal is not found, although it is derivable.
\<close>

lemma sym_not_found_in_smaller_universe:
  "\<not> gflood_decide base_hsig empty_axs ns5 40 [tp, tq, pq, qp, pp, e1, e2] ({pq}, qp)"
  by eval

lemma not_derivable_not_found:
  "\<not> gflood_decide base_hsig empty_axs ns5 40 U_sym ({}, qp)"
  by eval

text \<open>The successes are derivability theorems, by soundness for every universe.\<close>

lemma derivable_mp: "hol_lite.derivable base_hsig {} {pq, tp} tq"
  using search_base.gflood_decide_sound[OF mp_found] .

lemma derivable_sym: "hol_lite.derivable base_hsig {} {pq} qp"
  using search_base.gflood_decide_sound[OF sym_found] .

end
