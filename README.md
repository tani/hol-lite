# HOL-Lite: HOL Light's kernel and the Boyer-Moore waterfall in Isabelle/HOL

This repository contains

1. **`HOL_Lite_Kernel.thy`** – a function-by-function port of HOL Light's logical kernel
   (`fusion.ml`): types, terms, alpha-equivalence, `vsubst`/`inst`, theorems
   `Sequent hyps concl`, the ten primitive inference rules (`REFL`, `TRANS`, `MK_COMB`,
   `ABS`, `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST_TYPE`, `INST`) and the
   definitional principles (`new_axiom`, `new_basic_definition`,
   `new_basic_type_definition`, `new_type`, `new_constant`).
2. **`HOL_Lite_Bool.thy`** – HOL Light's derived logic (`equal.ml`/`bool.ml` style):
   `T`, `/\`, `==>`, `!`, `\/`, `F`, `~` are *defined* through the kernel and the usual rules
   (`SYM`, `BETA_CONV`, `EQT_*`, `CONJ`, `CONJUNCT1/2`, `MP`, `DISCH`, `SPEC`, `GEN`, `CONTR`,
   `NOT_*`, `DISJ1/2`, `DISJ_CASES`, `EXCLUDED_MIDDLE`, ...) are derived from them; a
   propositional tautology prover (`TAUT`), term matching, `REWR_CONV`, a bottom-up rewriter
   with conditional and permutative rules, and proof-producing conversion to clausal form.
3. **`HOL_Lite_Waterfall.thy`** – the waterfall of
   *The Boyer-Moore Waterfall Model Revisited* (Papapanagiotou & Fleuriot, arXiv:1808.03810),
   written as a tactic on top of that kernel: every heuristic produces subgoals together with a
   justification, and every theorem it returns was built by the kernel rules.

OCaml exceptions became `option`, OCaml's global references (`the_type_constants`, ...) are a
`kstate` record threaded through the extension principles, and the two non-structural
recursions of `fusion.ml` (`variant`, the capture-avoiding retry of `inst`) take a generous
fuel bound. Isabelle cannot hide the constructor of `hthm`, so, as in any shallow embedding of
LCF, soundness rests on only building theorems through the kernel functions. The one
classical axiom is `BOOL_CASES_AX` (HOL Light derives it from choice, `class.ml`); constants
have ASCII names (`AND`, `OR`, `IMP`, `ALL`, `NOT`, `T`, `F`).

## What is implemented from the paper

| Paper | Here |
|---|---|
| 3.2 Shell (constructors, bottom objects, accessors, induction, distinctness, one-one) | `shell` record; `nat_shell` (Peano arithmetic, with `+`, `*`, `<=`, `<`) and a polymorphic `list_shell` (`APPEND`, `REVERSE`, `LENGTH`); theory axioms via `new_axiom` |
| 3.1 waterfall, pool, induction on the pool | `pour`, `run_pipe`, `induct_prep` (induction through the shell's induction theorem, base/step cases as subgoals) |
| 3.3.1 Clausal form | `h_clausal` (CNF by rewriting with TAUT-proved equivalences, conjunction split) |
| 3.3.2 Substitution | `h_subst` |
| 3.3.3 Simplify | `h_simp` (user/definition rewrite rules, conditional and permutative rules, shell theorems) |
| 3.3.4 Equality (cross-fertilization) | `h_equal` (drops the induction hypothesis in step cases; explicit value templates excluded) |
| 3.3.5 Generalization (minimal common subterms, generalization lemmas) | `h_gen False` |
| 3.3.6 Irrelevance | `h_irrel` |
| 4.2.2 Loop elimination | warehouse filter (`run_pipe`), induction filter (`ih`), maximum term depth (`clause_depth`) |
| 4.3 Tautology and Setify heuristics | `h_taut`, `h_setify` |
| 4.4.1 Aderhold's common subterm generalization | `h_gen True` (single best proposal, no constructors, equation criterion; the induction test is omitted) |
| 4.4.2 Generalizing variables apart | `h_apart` |
| 4.4.3 Counterexample checker | `cex_check` (random ground instances from the shell's constructors, evaluated by the rewriter; undecidable instances are rejected) |
| 3.4 User interaction | choice and order of heuristics (`bm_order`, `bme_order`, `bmf_order`), rewrite rules, generalization lemmas |

## Results

`examples_BME` and `examples_BMF` in `HOL_Lite_Waterfall.thy` are checked when the session is
built (`by eval`): each prover run returns a hypothesis-free kernel theorem whose conclusion is
the goal. Steps / inductions / generalizations (BMF = `bmf_order`, otherwise `bme_order`):

| Theorem | steps | inds | gens |
|---|---|---|---|
| `m + 0 = m` | 5 | 1 | 0 |
| `m + (n + p) = (m + n) + p` | 5 | 1 | 0 |
| `m + n = n + m` | 15 | 3 | 0 |
| `m * n = n * m` | 27 | 5 | 2 |
| `m * (n + p) = m * n + m * p` | 22 | 4 | 2 |
| `(m * n) * p = m * (n * p)` (BMF) | 18 | 3 | 3 |
| `m + n = m + p <=> n = p` | 10 | 1 | 0 |
| `SUC m <= n <=> m < n` | 23 | 2 | 0 |
| `m < SUC n <=> m <= n` | 40 | 4 | 0 |
| `m <= n <=> m < n \/ m = n` | 37 | 4 | 0 |
| `LENGTH (REVERSE x) = LENGTH x` | 11 | 2 | 1 |
| `REVERSE (REVERSE x) = x` | 12 | 2 | 1 |

Known failures with the same setup: trichotomy `m < n \/ n < m \/ m = n`,
`REVERSE (APPEND x y) = APPEND (REVERSE y) (REVERSE x)`.

## Not covered

The 145-theorem evaluation, HOL Light's own simplifier (a small rewriter replaces it),
existential quantifiers, the shell's cases and type-axiom theorems (stored but unused), and
proofs *about* the kernel (consistency of the HOL Light logic is not mechanised here).

## Building

```
isabelle build -D .          # Isabelle2025-2; needs HOL-Library
```
