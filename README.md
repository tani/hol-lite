# HOL-Lite: HOL Light's kernel and the Boyer-Moore waterfall in Isabelle/HOL

This repository contains

1. **`HOL_Lite_Kernel.thy`** – a function-by-function port of HOL Light's logical kernel
   (`fusion.ml`): types, terms, alpha-equivalence, `variant`, `vsubst`, `inst`, theorems
   `Sequent hyps concl`, the ten primitive inference rules (`REFL`, `TRANS`, `MK_COMB`, `ABS`,
   `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST_TYPE`, `INST`) and the definitional
   principles (`new_axiom`, `new_basic_definition`, `new_basic_type_definition`, `new_type`,
   `new_constant`).
2. **`HOL_Lite_Bool.thy`** – ports of HOL Light's library on top of the kernel:
   `basics.ml` (matching of types, `subst`, `variants`, `find_terms`, ...), `equal.ml`
   (`THENC`, `ORELSEC`, `REPEATC`, `SUB_CONV`, `DEPTH_CONV`, `REDEPTH_CONV`, `TOP_DEPTH_CONV`,
   ...), `bool.ml` (`T`, `/\`, `==>`, `!`, `?`, `\/`, `F`, `~`, `?!` defined through the kernel, and the
   derived rules `CONJ`, `MP`, `DISCH`, `SPEC`, `GEN`, `CHOOSE`, `DISJ_CASES`, ...), `drule.ml`
   (higher-order `term_match`, `INSTANTIATE`, `PART_MATCH`), `simp.ml` (`REWR_CONV`,
   `GEN_REWRITE_CONV`, `REWRITE_CONV`, term nets, ordered rewriting of permutative rules),
   `tactics.ml` (the metavariable-free subset: `THEN`, `THENL`, `REPEAT`, `GEN_TAC`, `CONJ_TAC`,
   `DISJ_CASES_TAC`, `CHOOSE_TAC`, `SUBST1_TAC`, `STRUCT_CASES_TAC`, `REWRITE_TAC`, `prove`) and
   `class.ml`'s `TAUT` (`REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN REPEAT RTAUT_TAC`, using
   `BOOL_CASES_TAC`).
3. **`HOL_Lite_Waterfall.thy`** – the waterfall of
   *The Boyer-Moore Waterfall Model Revisited* (Papapanagiotou & Fleuriot, arXiv:1808.03810),
   written as a tactic on top of that kernel: every heuristic produces subgoals together with a
   justification, and every theorem it returns was built by the kernel rules. Simplification
   uses the ported `REWRITE_CONV`, clausal form `PURE_REWRITE_CONV` with rules proved by `TAUT`,
   generalization lemmas `term_match`/`INSTANTIATE`.

## Fidelity to HOL Light

* OCaml exceptions became `option`; OCaml's global references (`the_type_constants`, ...) are a
  `kstate` record threaded through the extension principles.
* The non-structural recursions are ported **without fuel**: `variant` is a `function` with a
  termination proof, and `inst` (capture-avoiding retry) and the depth conversions, `REPEAT`,
  `deep_alpha`, `term_match` are `partial_function (option)`s. A looping conversion is
  nontermination, as in OCaml, and is distinct from failure (the result type is `'a option
  option`; the wrappers expose the usual `conv = term ⇒ thm option`).
* The one classical axiom is `BOOL_CASES_AX` (HOL Light derives it from `SELECT_AX`/choice);
  everything else in `bool.ml` is derived. Constants have ASCII names (`AND`, `OR`, `IMP`, `ALL`,
  `EX`, `EXU`, `NOT`, `T`, `F`).
* Isabelle cannot hide the constructor of `hthm`, so, as in any shallow embedding of LCF,
  soundness rests on building theorems only through the kernel functions.

Remaining deviations: the kernel orders terms with a serialized comparison instead of OCaml's
polymorphic `compare`; term nets are association lists; `mk_rewrites` omits the `cf=true` case
(`CONJ` of conditionals); tactics carry no metavariables (so no `ITAUT`/`MESON`; the clause theorems
`REFL_CLAUSE`, `EQ_CLAUSES`, `NOT_CLAUSES`, `AND/OR/IMP_CLAUSES`, ... are proved by a small
ground-evaluation prover `BS_TAUT` that is only used to bootstrap `REWRITE_CONV` before `TAUT`
exists); `STRUCT_CASES_THEN` is size-bounded rather than a `REPEAT_TCL`.

## What is implemented from the paper

| Paper | Here |
|---|---|
| 3.2 Shell (constructors, bottom objects, accessors, induction, distinctness, one-one) | `shell` record; `nat_shell` (Peano arithmetic, with `+`, `*` as in HOL Light, `<=`, `<`) and a polymorphic `list_shell` (`APPEND`, `REVERSE`, `LENGTH`); theory axioms via `new_axiom` |
| 3.1 waterfall, pool, induction on the pool | `pour`, `run_pipe`, `induct_prep` (induction through the shell's induction theorem, base/step cases as subgoals) |
| 3.3.1 Clausal form | `h_clausal` (`PURE_REWRITE_CONV` with `TAUT`-proved equivalences, conjunction split) |
| 3.3.2 Substitution | `h_subst` |
| 3.3.3 Simplify | `h_simp` (`REWRITE_CONV` with the definitions, shell theorems and conditional / permutative rules) |
| 3.3.4 Equality (cross-fertilization) | `h_equal` |
| 3.3.5 Generalization (minimal common subterms, generalization lemmas) | `h_gen False` |
| 3.3.6 Irrelevance | `h_irrel` |
| 4.2.2 Loop elimination | warehouse filter (`run_pipe`), induction filter, maximum term depth |
| 4.3 Tautology and Setify heuristics | `h_taut`, `h_setify` |
| 4.4.1 Aderhold's common subterm generalization | `h_gen True`: generalizable terms exclude constructors; proposals from recursive argument positions and equation sides (`node_proposals`, `side_proposals`); suitability (≥ 2 occurrences, equation criterion); ranking by induction test, times proposed, occurrences (`ad_key`); only the best proposal is applied; generalized terms are remembered; counterexample filter |
| 4.4.2 Generalizing variables apart | `h_apart` |
| 4.4.3 Counterexample checker | `cex_check` (random ground instances, evaluated by `REWRITE_CONV`; undecidable instances are rejected) |
| 3.4 User interaction | choice and order of heuristics (`bm_order`, `bme_order`, `bmf_order`), rewrite rules, generalization lemmas |

## Results

`examples_BME` and `examples_BMF` in `HOL_Lite_Waterfall.thy` are checked when the session is
built (`by eval`): each prover run returns a hypothesis-free kernel theorem whose conclusion is
the goal. Steps / inductions / generalizations:

| Theorem | order | steps | inds | gens |
|---|---|---|---|---|
| `m + 0 = m` | BME | 5 | 1 | 0 |
| `m + (n + p) = (m + n) + p` | BME | 5 | 1 | 0 |
| `m + n = n + m` | BME | 15 | 3 | 0 |
| `m * n = n * m` | BME / BMF | 37 | 7 | 1 |
| `m * (n + p) = m * n + m * p` | BME | 22 | 4 | 2 |
| `(m * n) * p = m * (n * p)` | BMF | 33 | 6 | 3 |
| `m + n = m + p <=> n = p` | BME | 10 | 1 | 0 |
| `SUC m <= n <=> m < n` | BME | 23 | 2 | 0 |
| `m < SUC n <=> m <= n` | BME | 40 | 4 | 0 |
| `m <= n <=> m < n \/ m = n` | BME | 37 | 4 | 0 |
| `LENGTH (REVERSE x) = LENGTH x` | BME | 11 | 2 | 1 |
| `REVERSE (REVERSE x) = x` | BME / BMF | 12 | 2 | 1 |

For `m * n = n * m` the Aderhold step generalizes `m * n` in
`((m * n) + n') + SUC n'' = ((m * n) + n'') + SUC n'`, exactly the example of the paper.

## Not covered

The 145-theorem evaluation, existential quantifiers in the waterfall, the shell's cases and
type-axiom theorems (stored but unused), and proofs *about* the kernel (consistency of the HOL
Light logic is not mechanised here).

## Building

```
isabelle build -D .          # Isabelle2025-2; needs HOL-Library
```
