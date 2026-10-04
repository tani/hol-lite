theory HOL_Lite_Waterfall
  imports HOL_Lite_Bool
begin

text \<open>
  The Boyer-Moore waterfall of "The Boyer-Moore Waterfall Model Revisited"
  (Papapanagiotou & Fleuriot), built as a proof-producing tactic on top of the HOL Light
  kernel port.  Every heuristic returns either a theorem, or subgoals together with a
  justification that rebuilds a theorem of the goal from theorems of the subgoals; all
  theorems are constructed by the kernel rules, so the prover cannot return a wrong theorem.

  Contents (section numbers refer to the paper):
  Section 3.2 shells;  3.3.1 clausal form;  3.3.2 substitution;
  3.3.3 simplify;  3.3.4 equality (cross-fertilization);
  3.3.5 generalization (minimal common subterms, generalization lemmas);
  3.3.6 irrelevance;  4.2.2 warehouse filter and maximum term depth;
  4.3 tautology and setify heuristics;  4.4.1 Aderhold's common subterm
  generalization;  4.4.2 generalizing variables apart;  4.4.3 the
  counterexample checker; induction on the pool.
\<close>

section \<open>Clause and conjunction helpers\<close>

primrec dest_conjuncts :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "dest_conjuncts 0 tm = [tm]"
| "dest_conjuncts (Suc n) tm =
     (case dest_conj tm of
        Some (a, b) \<Rightarrow> dest_conjuncts n a @ dest_conjuncts n b
      | None \<Rightarrow> [tm])"

primrec dest_disjuncts :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "dest_disjuncts 0 tm = [tm]"
| "dest_disjuncts (Suc n) tm =
     (case dest_disj tm of
        Some (a, b) \<Rightarrow> dest_disjuncts n a @ dest_disjuncts n b
      | None \<Rightarrow> [tm])"

definition conjuncts :: "hterm \<Rightarrow> hterm list" where
  "conjuncts tm = dest_conjuncts (tm_size tm) tm"

definition disjuncts :: "hterm \<Rightarrow> hterm list" where
  "disjuncts tm = dest_disjuncts (tm_size tm) tm"

definition mk_clause :: "hterm list \<Rightarrow> hterm" where
  "mk_clause lits =
     (case rev lits of
        [] \<Rightarrow> F_tm
      | l # ls \<Rightarrow> foldl (\<lambda>acc a. mk_disj a acc) l ls)"

definition mk_conj_list :: "hterm list \<Rightarrow> hterm" where
  "mk_conj_list ts =
     (case rev ts of
        [] \<Rightarrow> T_tm
      | l # ls \<Rightarrow> foldl (\<lambda>acc a. mk_conj a acc) l ls)"

fun strip_conds :: "hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_conds (Comb (Comb (Const n ty) c) r) =
     (if n = ''IMP'' then (case strip_conds r of (cs, e) \<Rightarrow> (c # cs, e))
      else ([], Comb (Comb (Const n ty) c) r))"
| "strip_conds tm = ([], tm)"

fun type_of_args :: "hol_type \<Rightarrow> hol_type list" where
  "type_of_args (Tyapp c [a, b]) = (if c = ''fun'' then a # type_of_args b else [])"
| "type_of_args _ = []"

section \<open>Shells (Section 3.2)\<close>

record shell =
  sh_name :: string
  sh_ty :: hol_type
  sh_bottoms :: "hterm list"
  sh_cons :: "hterm list"
  sh_accs :: "hterm list"
  sh_type_axiom :: "hthm option"
  sh_induct :: hthm
  sh_cases :: "hthm option"
  sh_distinct :: "hthm list"
  sh_oneone :: "hthm list"
  sh_accdefs :: "hthm list"

fun const_name :: "hterm \<Rightarrow> string option" where
  "const_name (Const n _) = Some n"
| "const_name _ = None"

definition shell_con_names :: "shell \<Rightarrow> string list" where
  "shell_con_names sh = List.map_filter const_name (sh_bottoms sh @ sh_cons sh)"

definition shell_acc_names :: "shell \<Rightarrow> string list" where
  "shell_acc_names sh = List.map_filter const_name (sh_accs sh)"

definition is_con_name :: "shell list \<Rightarrow> string \<Rightarrow> bool" where
  "is_con_name shs n = list_ex (\<lambda>sh. n \<in> set (shell_con_names sh)) shs"

definition is_acc_name :: "shell list \<Rightarrow> string \<Rightarrow> bool" where
  "is_acc_name shs n = list_ex (\<lambda>sh. n \<in> set (shell_acc_names sh)) shs"

text \<open>Explicit value templates: non-variable terms made of constants, or constructors
  applied to bottom objects or variables.\<close>

primrec is_template_n :: "nat \<Rightarrow> shell list \<Rightarrow> hterm \<Rightarrow> bool" where
  "is_template_n 0 shs t = False"
| "is_template_n (Suc k) shs t =
     (case strip_comb t of
        (Const n _, args) \<Rightarrow>
          is_con_name shs n \<and> list_all (\<lambda>a. is_var a \<or> is_template_n k shs a) args
      | _ \<Rightarrow> False)"

definition is_template :: "shell list \<Rightarrow> hterm \<Rightarrow> bool" where
  "is_template shs t = is_template_n (tm_size t) shs t"

definition is_accessor_app :: "shell list \<Rightarrow> hterm \<Rightarrow> bool" where
  "is_accessor_app shs t = (case strip_comb t of (Const n _, _ # _) \<Rightarrow> is_acc_name shs n | _ \<Rightarrow> False)"

primrec has_con_n :: "nat \<Rightarrow> shell list \<Rightarrow> hterm \<Rightarrow> bool" where
  "has_con_n 0 shs t = False"
| "has_con_n (Suc k) shs t =
     (case t of
        Const n _ \<Rightarrow> is_con_name shs n
      | Comb f x \<Rightarrow> has_con_n k shs f \<or> has_con_n k shs x
      | Abs _ b \<Rightarrow> has_con_n k shs b
      | Var _ _ \<Rightarrow> False)"

definition has_constructor :: "shell list \<Rightarrow> hterm \<Rightarrow> bool" where
  "has_constructor shs t = has_con_n (tm_size t) shs t"

section \<open>Contexts, states and heuristics\<close>

datatype heur =
    H_Clausal | H_Taut | H_Setify | H_Subst | H_Simp | H_Equal
  | H_GenBM | H_GenAd | H_GenApart | H_Irrel

definition pp_heur :: "heur \<Rightarrow> string" where
  "pp_heur h =
     (case h of
        H_Clausal \<Rightarrow> ''Clausal Form Heuristic'' | H_Taut \<Rightarrow> ''Tautology Heuristic''
      | H_Setify \<Rightarrow> ''Setify Heuristic'' | H_Subst \<Rightarrow> ''Substitution Heuristic''
      | H_Simp \<Rightarrow> ''Simplify Heuristic'' | H_Equal \<Rightarrow> ''Equality Heuristic''
      | H_GenBM \<Rightarrow> ''Generalization Heuristic'' | H_GenAd \<Rightarrow> ''Common Subterm Generalization''
      | H_GenApart \<Rightarrow> ''Generalizing Variables Apart'' | H_Irrel \<Rightarrow> ''Irrelevance Heuristic'')"

record wctx =
  w_shells :: "shell list"
  w_rules :: "hthm list"
  w_glemmas :: "(hthm \<times> hterm) list"
  w_order :: "heur list"
  w_maxdepth :: nat
  w_ncex :: nat

record wst =
  w_trace :: "string list"
  w_steps :: nat
  w_inds :: nat
  w_gens :: nat
  w_overs :: nat
  w_seed :: nat
  w_gened :: "hterm list"

definition init_wst :: wst where
  "init_wst = \<lparr> w_trace = [], w_steps = 0, w_inds = 0, w_gens = 0, w_overs = 0, w_seed = 42, w_gened = [] \<rparr>"

definition add_note :: "string \<Rightarrow> wst \<Rightarrow> wst" where
  "add_note s st = st\<lparr> w_trace := s # w_trace st \<rparr>"

text \<open>The outcome of a heuristic: failure (pass the clause on), a proof, disproof, or
  subgoals with a justification.\<close>

datatype hres =
    HFail
  | HProved hthm
  | HDisproved
  | HSub "hterm list" "hthm list \<Rightarrow> hthm option"

section \<open>Clause manipulation with proof\<close>

definition lit_atom :: "hterm \<Rightarrow> hterm" where
  "lit_atom l = (case dest_neg l of Some a \<Rightarrow> a | None \<Rightarrow> l)"

definition remove_first :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "remove_first x ls =
     (case find (\<lambda>y. aconv x y) ls of
        None \<Rightarrow> ls
      | Some _ \<Rightarrow> (let i = length (takeWhile (\<lambda>y. \<not> aconv x y) ls) in take i ls @ drop (Suc i) ls))"

text \<open>@{text embed}: from @{text "\<Gamma> \<turnstile> l"} derive @{text "\<Gamma> \<turnstile> C"} when @{text l} is
  (alpha-equivalent to) one of the disjuncts of the clause @{text C}.\<close>

primrec embed_n :: "nat \<Rightarrow> hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "embed_n 0 th c = (if aconv (concl th) c then Some th else None)"
| "embed_n (Suc k) th c =
     (if aconv (concl th) c then Some th
      else case dest_disj c of
        None \<Rightarrow> None
      | Some (a, b) \<Rightarrow>
          (case embed_n k th a of
             Some t \<Rightarrow> DISJ1 t b
           | None \<Rightarrow> (case embed_n k th b of Some t \<Rightarrow> DISJ2 a t | None \<Rightarrow> None)))"

definition embed :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "embed th c = embed_n (tm_size c) th c"

text \<open>@{text weaken}: from @{text "\<turnstile> C'"}, where every disjunct of @{text C'} is a disjunct
  of @{text C}, derive @{text "\<turnstile> C"}.\<close>

primrec weaken_n :: "nat \<Rightarrow> hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "weaken_n 0 th c = (if aconv (concl th) c then Some th else embed th c)"
| "weaken_n (Suc k) th c =
     (if aconv (concl th) c then Some th
      else case dest_disj (concl th) of
        None \<Rightarrow> embed th c
      | Some (a, b) \<Rightarrow>
          do { aa \<leftarrow> ASSUME a;
               ab \<leftarrow> ASSUME b;
               c1 \<leftarrow> weaken_n k aa c;
               c2 \<leftarrow> weaken_n k ab c;
               DISJ_CASES th c1 c2 })"

definition weaken :: "hthm \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "weaken th c = weaken_n (tm_size (concl th) + 1) th c"

definition frees_of_list :: "hterm list \<Rightarrow> hterm list" where
  "frees_of_list ts = freesl ts"

section \<open>Clausal form (3.3.1)\<close>

primrec build_conj_n :: "nat \<Rightarrow> hterm \<Rightarrow> hthm list \<Rightarrow> (hthm \<times> hthm list) option" where
  "build_conj_n 0 tm ths = (case ths of t # r \<Rightarrow> Some (t, r) | [] \<Rightarrow> None)"
| "build_conj_n (Suc k) tm ths =
     (case dest_conj tm of
        Some (a, b) \<Rightarrow>
          do { (ta, r1) \<leftarrow> build_conj_n k a ths;
               (tb, r2) \<leftarrow> build_conj_n k b r1;
               t \<leftarrow> CONJ ta tb;
               Some (t, r2) }
      | None \<Rightarrow> (case ths of t # r \<Rightarrow> Some (t, r) | [] \<Rightarrow> None))"

definition build_conj :: "hterm \<Rightarrow> hthm list \<Rightarrow> hthm option" where
  "build_conj tm ths = map_option fst (build_conj_n (tm_size tm) tm ths)"

definition h_clausal :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_clausal cx ind tm =
     (case cnf_conv tm of
        None \<Rightarrow> HFail
      | Some th \<Rightarrow>
          (case rhs th of
             None \<Rightarrow> HFail
           | Some tm' \<Rightarrow>
               if aconv tm tm' then HFail
               else if tm' = T_tm then (case EQT_ELIM th of Some r \<Rightarrow> HProved r | None \<Rightarrow> HFail)
               else HSub (conjuncts tm')
                      (\<lambda>ths. do { cj \<leftarrow> build_conj tm' ths; sy \<leftarrow> SYM th; EQ_MP sy cj })))"

section \<open>Tautology and setify (4.3.1, 4.3.3)\<close>

text \<open>The Tautology heuristic runs HOL Light's general propositional tautology prover
  (@{const TAUT}: rewriting plus case splits on the boolean subterms) on the clause, so that any
  propositional tautology over the clause's atoms is proved, not only those with a literal pair
  @{text "p, \<not>p"}, @{text T} or @{text "x = x"}.  As the prover splits on every atom, it is only
  attempted for clauses with at most @{text max_taut_atoms} atoms.\<close>

definition max_taut_atoms :: nat where "max_taut_atoms = 12"

definition h_taut :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_taut cx ind tm =
     (if length (bool_atoms tm) > max_taut_atoms then HFail
      else case TAUT tm of Some th \<Rightarrow> HProved th | None \<Rightarrow> HFail)"

fun dedup_aconv :: "hterm list \<Rightarrow> hterm list" where
  "dedup_aconv [] = []"
| "dedup_aconv (x # xs) = x # dedup_aconv (filter (\<lambda>y. \<not> aconv x y) xs)"

definition h_setify :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_setify cx ind tm =
     (let ls = disjuncts tm; ls' = dedup_aconv ls in
      if length ls' = length ls then HFail
      else HSub [mk_clause ls'] (\<lambda>ths. case ths of [th] \<Rightarrow> weaken th tm | _ \<Rightarrow> None))"

section \<open>Substitution (3.3.2) and equality (3.3.4)\<close>

text \<open>Both heuristics use a negated equation @{text "\<not>(a = b)"} of the clause: in the case
  @{text "a = b"} the remaining literals may be rewritten with it; otherwise the negated
  equation itself closes the clause.\<close>

definition neg_eq_parts :: "hterm \<Rightarrow> (hterm \<times> hterm \<times> hterm) option" where
  "neg_eq_parts l = (case dest_neg l of Some e \<Rightarrow> (case dest_eq e of Some (x, y) \<Rightarrow> Some (e, x, y) | None \<Rightarrow> None) | None \<Rightarrow> None)"

definition orient :: "bool \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "orient swap e = do { a \<leftarrow> ASSUME e; if swap then SYM a else Some a }"

text \<open>Given the clause @{text tm}, the literal @{text l} (a negated equation @{text e}) and the
  oriented hypothesis @{text "{e} \<turnstile> a = b"}: rewrite the rest of the clause.  The justification
  turns a theorem of the rewritten rest into a theorem of the clause.\<close>

text \<open>Replacement restricted to one side of the equations of a clause: @{text mode} 0 replaces
  everywhere, 1 only in right-hand sides and 2 only in left-hand sides of equations.\<close>

primrec replace_side_n :: "nat \<Rightarrow> hthm \<Rightarrow> nat \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "replace_side_n 0 th mode tm = Some (REFL tm)"
| "replace_side_n (Suc k) th mode tm =
     (case lhs th of
        None \<Rightarrow> None
      | Some a \<Rightarrow>
          if mode = 0 then replace_conv th tm
          else
            (case dest_eq tm of
               Some (x, y) \<Rightarrow>
                 (case tm of
                    Comb c _ \<Rightarrow>
                      (if mode = 1 then do { ty \<leftarrow> replace_conv th y; AP_TERM c ty }
                       else (case c of
                               Comb c0 _ \<Rightarrow> do { tx \<leftarrow> replace_conv th x; a1 \<leftarrow> AP_TERM c0 tx; AP_THM a1 y }
                             | _ \<Rightarrow> None))
                  | _ \<Rightarrow> None)
             | None \<Rightarrow>
                 (case tm of
                    Comb s t \<Rightarrow> do { a1 \<leftarrow> replace_side_n k th mode s; a2 \<leftarrow> replace_side_n k th mode t; MK_COMB a1 a2 }
                  | _ \<Rightarrow> Some (REFL tm))))"

definition rewrite_rest ::
  "hterm \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> (hterm list \<times> (hthm list \<Rightarrow> hthm option)) option" where
  "rewrite_rest tm l e swap keep_lit need_change mode =
     (let ls = disjuncts tm; rest_ls = remove_first l ls in
      if rest_ls = [] then None
      else
        let rest = mk_clause rest_ls in
        do { th_o \<leftarrow> orient swap e;
             eqr \<leftarrow> replace_side_n (tm_size rest + 2) th_o mode rest;
             rest' \<leftarrow> rhs eqr;
             (if need_change \<and> aconv rest rest' then None else
              let goal = (if keep_lit then mk_disj l rest' else rest') in
              Some ([goal],
                    (\<lambda>ths.
                      case ths of
                        [th'] \<Rightarrow>
                          do { sy \<leftarrow> SYM eqr;
                               c2 \<leftarrow> (let al = ASSUME l in
                                     do { a_l \<leftarrow> al; embed a_l tm });
                               em \<leftarrow> SPEC e EXCLUDED_MIDDLE;
                               c1 \<leftarrow> (if keep_lit
                                     then do { a_l \<leftarrow> ASSUME l;
                                               cl \<leftarrow> embed a_l tm;
                                               ar \<leftarrow> ASSUME rest';
                                               rr \<leftarrow> EQ_MP sy ar;
                                               cr \<leftarrow> weaken rr tm;
                                               DISJ_CASES th' cl cr }
                                     else do { r \<leftarrow> EQ_MP sy th'; weaken r tm });
                               DISJ_CASES em c1 c2 }
                      | _ \<Rightarrow> None))) })"

definition h_subst :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_subst cx ind tm =
     (let ls = disjuncts tm;
          cands = List.map_filter
                    (\<lambda>l. case neg_eq_parts l of
                           Some (e, x, y) \<Rightarrow>
                             (if is_var x \<and> x \<notin> set (frees y) then Some (l, e, False)
                              else if is_var y \<and> y \<notin> set (frees x) then Some (l, e, True)
                              else None)
                         | None \<Rightarrow> None) ls;
          tries = List.map_filter (\<lambda>(l, e, sw). rewrite_rest tm l e sw False False 0) cands
      in case tries of
           [] \<Rightarrow> HFail
         | (gs, j) # _ \<Rightarrow> HSub gs j)"

definition h_equal :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_equal cx ind tm =
     (let ls = disjuncts tm;
          shs = w_shells cx;
          cands = concat (List.map_filter
                    (\<lambda>l. case neg_eq_parts l of
                           Some (e, x, y) \<Rightarrow>
                             (let mk = (\<lambda>a sw. if is_template shs a \<or> aconv x y then []
                                               else if is_var a then [(l, e, sw, 1::nat), (l, e, sw, 2)]
                                               else [(l, e, sw, 0)])
                              in Some (mk x False @ mk y True))
                         | None \<Rightarrow> None) ls);
          tries = List.map_filter
                    (\<lambda>(l, e, sw, md).
                       (case rewrite_rest tm l e sw (\<not> ind) True md of
                          Some (gs, j) \<Rightarrow>
                            (case gs of
                               [g] \<Rightarrow> (if aconv g tm then None else Some (gs, j))
                             | _ \<Rightarrow> None)
                        | None \<Rightarrow> None)) cands
      in case tries of
           [] \<Rightarrow> HFail
         | (gs, j) # _ \<Rightarrow> HSub gs j)"

section \<open>Simplify (3.3.3)\<close>

definition h_simp :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_simp cx ind tm =
     (case REWRITE_CONV (w_rules cx) tm of
        None \<Rightarrow> HFail
      | Some th \<Rightarrow>
          (case rhs th of
             None \<Rightarrow> HFail
           | Some tm' \<Rightarrow>
               if aconv tm tm' then HFail
               else if tm' = T_tm then (case EQT_ELIM th of Some r \<Rightarrow> HProved r | None \<Rightarrow> HFail)
               else if tm' = F_tm then HDisproved
               else HSub [tm'] (\<lambda>ths. case ths of [t] \<Rightarrow> (do { sy \<leftarrow> SYM th; EQ_MP sy t }) | _ \<Rightarrow> None)))"

section \<open>Irrelevance (3.3.6)\<close>

primrec consts_of_n :: "nat \<Rightarrow> hterm \<Rightarrow> string list" where
  "consts_of_n 0 t = []"
| "consts_of_n (Suc k) t =
     (case t of
        Const n _ \<Rightarrow> [n]
      | Comb f x \<Rightarrow> consts_of_n k f @ consts_of_n k x
      | Abs _ b \<Rightarrow> consts_of_n k b
      | Var _ _ \<Rightarrow> [])"

definition consts_of :: "hterm \<Rightarrow> string list" where
  "consts_of t = consts_of_n (tm_size t) t"

definition logical_names :: "string list" where
  "logical_names = [''='', ''NOT'', ''OR'', ''AND'', ''IMP'', ''ALL'', ''T'', ''F'']"

text \<open>Partition literals into groups sharing variables.\<close>

primrec merge_parts_n :: "nat \<Rightarrow> (hterm list \<times> hterm list) list \<Rightarrow> (hterm list \<times> hterm list) list" where
  "merge_parts_n 0 ps = ps"
| "merge_parts_n (Suc k) ps =
     (case ps of
        [] \<Rightarrow> []
      | (ls, vs) # rest \<Rightarrow>
          (let shared = filter (\<lambda>p. list_ex (\<lambda>v. v \<in> set vs) (snd p)) rest;
               others = filter (\<lambda>p. \<not> list_ex (\<lambda>v. v \<in> set vs) (snd p)) rest
           in if shared = [] then (ls, vs) # merge_parts_n k others
              else merge_parts_n k ((ls @ concat (map fst shared), vs @ concat (map snd shared)) # others)))"

definition merge_parts :: "(hterm list \<times> hterm list) list \<Rightarrow> (hterm list \<times> hterm list) list" where
  "merge_parts ps = merge_parts_n (length ps + 1) ps"

definition lit_is_var_app :: "hterm \<Rightarrow> bool" where
  "lit_is_var_app l =
     (case strip_comb (lit_atom l) of
        (Const n _, args) \<Rightarrow> n \<notin> set logical_names \<and> args \<noteq> [] \<and> list_all is_var args \<and> distinct args
      | _ \<Rightarrow> False)"

definition h_irrel :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> hres" where
  "h_irrel cx ind tm =
     (let ls = disjuncts tm;
          shs = w_shells cx;
          shell_names = concat (map (\<lambda>sh. shell_con_names sh @ shell_acc_names sh) shs) @ logical_names;
          parts = merge_parts (map (\<lambda>l. ([l], frees l)) ls);
          irrelevant = (\<lambda>p. list_all (\<lambda>l. list_all (\<lambda>n. n \<in> set shell_names) (consts_of l)) (fst p)
                            \<or> (length (fst p) = 1 \<and> list_ex lit_is_var_app (fst p)));
          keep = filter (\<lambda>p. \<not> irrelevant p) parts
      in if length keep = length parts then HFail
         else if keep = [] then HDisproved
         else
           let ls' = concat (map fst keep) in
           HSub [mk_clause ls']
                (\<lambda>ths. case ths of [th] \<Rightarrow> weaken th tm | _ \<Rightarrow> None))"


section \<open>Counterexample checker (4.4.3)\<close>

fun nat_str :: "nat \<Rightarrow> string" where
  "nat_str n = (if n < 10 then [char_of (48 + n)] else nat_str (n div 10) @ [char_of (48 + n mod 10)])"

definition rnd :: "nat \<Rightarrow> nat" where
  "rnd s = (s * 1103515245 + 12345) mod 2147483648"

definition pick :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "pick k xs = (if xs = [] then None else Some (xs ! (k mod length xs)))"

text \<open>Random ground values of a shell type, built from its constructors.  The probability of
  choosing a bottom object grows as the depth bound is approached.\<close>

primrec gen_val_n :: "nat \<Rightarrow> shell \<Rightarrow> nat \<Rightarrow> hterm option \<times> nat" where
  "gen_val_n 0 sh seed = (pick (rnd seed div 65536) (sh_bottoms sh), rnd seed)"
| "gen_val_n (Suc d) sh seed =
     (let s1 = rnd seed; k = s1 div 65536 in
      if k mod (d + 2) = 0 \<or> sh_cons sh = [] then (pick k (sh_bottoms sh), s1)
      else
        (case pick k (sh_cons sh) of
           None \<Rightarrow> (None, s1)
         | Some c \<Rightarrow>
             (let tys = type_of_args (type_of c) in
              case foldl (\<lambda>acc ty.
                            case acc of
                              (None, s) \<Rightarrow> (None, s)
                            | (Some args, s) \<Rightarrow>
                                if ty = sh_ty sh
                                then (case gen_val_n d sh s of
                                        (Some a, s') \<Rightarrow> (Some (args @ [a]), s')
                                      | (None, s') \<Rightarrow> (None, s'))
                                else (Some (args @ [Var (''e'' @ nat_str s) ty]), rnd s)) (Some [], s1) tys of
                (Some args, s2) \<Rightarrow> (list_mk_comb c args, s2)
              | (None, s2) \<Rightarrow> (None, s2))))"

definition shell_of_type :: "shell list \<Rightarrow> hol_type \<Rightarrow> shell option" where
  "shell_of_type shs ty = find (\<lambda>sh. sh_ty sh = ty) shs"

definition ground_clause ::
  "wctx \<Rightarrow> hterm \<Rightarrow> nat \<Rightarrow> (hterm option \<times> nat)" where
  "ground_clause cx tm seed =
     (let vs = frees tm;
          r = foldl (\<lambda>acc v.
                       case acc of
                         (None, s) \<Rightarrow> (None, s)
                       | (Some th, s) \<Rightarrow>
                           (case shell_of_type (w_shells cx) (type_of v) of
                              None \<Rightarrow> (Some th, s)
                            | Some sh \<Rightarrow>
                                (case gen_val_n 4 sh s of
                                   (Some t, s') \<Rightarrow> (Some (th @ [(t, v)]), s')
                                 | (None, s') \<Rightarrow> (None, s')))) (Some [], seed) vs
      in case r of
           (Some theta, s) \<Rightarrow> (vsubst_checked theta tm, s)
         | (None, s) \<Rightarrow> (None, s))"

text \<open>A clause is refuted (or rejected as unsafe to generalize to) if some random ground
  instance does not evaluate to @{text T}; as in the paper, a ground clause that cannot be
  decided by the rewrite rules is also treated as unsafe.\<close>

primrec cex_check :: "nat \<Rightarrow> wctx \<Rightarrow> hterm \<Rightarrow> nat \<Rightarrow> bool \<times> nat" where
  "cex_check 0 cx tm seed = (False, seed)"
| "cex_check (Suc k) cx tm seed =
     (case ground_clause cx tm seed of
        (None, s) \<Rightarrow> (True, s)
      | (Some g, s) \<Rightarrow>
          (case REWRITE_CONV (w_rules cx) g of
             Some th \<Rightarrow>
               (case rhs th of
                  Some r \<Rightarrow> if r = T_tm then cex_check k cx tm s else (True, s)
                | None \<Rightarrow> (True, s))
           | None \<Rightarrow> (True, s)))"

definition unsafe_to_generalize :: "wctx \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> bool \<times> wst" where
  "unsafe_to_generalize cx tm st =
     (case cex_check (w_ncex cx) cx tm (w_seed st) of
        (b, s) \<Rightarrow> (b, st\<lparr> w_seed := s \<rparr>))"

section \<open>Generalization (3.3.5, 4.4.1)\<close>

primrec subs_n :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list" where
  "subs_n 0 t = [t]"
| "subs_n (Suc k) t = t # concat (map (\<lambda>a. subs_n k a) (snd (strip_comb t)))"

definition subs :: "hterm \<Rightarrow> hterm list" where
  "subs t = subs_n (tm_size t) t"

definition lit_roots :: "hterm \<Rightarrow> hterm list" where
  "lit_roots l =
     (let a = lit_atom l in
      case dest_eq a of Some (x, y) \<Rightarrow> [x, y] | None \<Rightarrow> snd (strip_comb a))"

definition gen_ok :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> bool" where
  "gen_ok cx ad t =
     (let shs = w_shells cx in
      \<not> is_var t \<and> \<not> is_template shs t \<and> \<not> is_accessor_app shs t
      \<and> (case t of Comb _ _ \<Rightarrow> True | _ \<Rightarrow> False)
      \<and> (\<not> ad \<or> \<not> has_constructor shs t))"

definition gen_terms :: "wctx \<Rightarrow> bool \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "gen_terms cx ad ls = filter (gen_ok cx ad) (concat (map subs (concat (map lit_roots ls))))"

definition count_in :: "hterm \<Rightarrow> hterm list \<Rightarrow> nat" where
  "count_in g us = length (filter (\<lambda>u. g \<in> set (subs u)) us)"

definition occ_count :: "hterm \<Rightarrow> hterm list \<Rightarrow> nat" where
  "occ_count g ts = length (filter (\<lambda>u. u = g) ts)"

definition on_both_sides :: "hterm \<Rightarrow> hterm list \<Rightarrow> bool" where
  "on_both_sides g ls =
     list_ex (\<lambda>l. case dest_eq (lit_atom l) of
                    Some (x, y) \<Rightarrow> g \<in> set (subs x) \<and> g \<in> set (subs y)
                  | None \<Rightarrow> False) ls"

definition twice_on_a_side :: "hterm \<Rightarrow> hterm list \<Rightarrow> bool" where
  "twice_on_a_side g ls =
     list_ex (\<lambda>l. case dest_eq (lit_atom l) of
                    Some (x, y) \<Rightarrow> occ_count g (subs x) \<ge> 2 \<or> occ_count g (subs y) \<ge> 2
                  | None \<Rightarrow> False) ls"

text \<open>Boyer-Moore generalization (3.3.5): a generalizable term is a candidate if it
  appears in more than one generalizable subterm, or on both sides of an equation or negated
  equation.  The minimal candidates (those having no other candidate as a proper subterm) are
  all generalized simultaneously.\<close>

definition gen_cands :: "wctx \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "gen_cands cx ls =
     (let gts = gen_terms cx False ls;
          cs = filter (\<lambda>g. count_in g gts \<ge> 2 \<or> on_both_sides g ls) (dedup_aconv gts)
      in filter (\<lambda>c. \<not> list_ex (\<lambda>c'. \<not> aconv c c' \<and> c' \<in> set (tl (subs c))) cs) cs)"

primrec rep_tm :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "rep_tm a b (Var n ty) = (if Var n ty = a then b else Var n ty)"
| "rep_tm a b (Const n ty) = (if Const n ty = a then b else Const n ty)"
| "rep_tm a b (Comb s t) = (if Comb s t = a then b else Comb (rep_tm a b s) (rep_tm a b t))"
| "rep_tm a b (Abs v t) = (if Abs v t = a then b else Abs v (rep_tm a b t))"

definition rep_pairs :: "(hterm \<times> hterm) list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "rep_pairs ps tm = foldl (\<lambda>acc p. rep_tm (fst p) (snd p) acc) tm ps"

text \<open>Fresh variables for the selected terms.\<close>

definition fresh_vars :: "hterm list \<Rightarrow> hterm list \<Rightarrow> (hterm \<times> hterm) list" where
  "fresh_vars avoid gs =
     snd (foldl (\<lambda>(av, acc) g.
                   (let v = variant av (Var ''n'' (type_of g)) in (v # av, acc @ [(g, v)])))
                (avoid, []) gs)"

text \<open>Generalization lemmas @{text "(\<turnstile> P, pattern)"}: if the generalized term is an instance of
  the pattern, the corresponding instance of the lemma is added as a hypothesis.\<close>

definition inst_by_match :: "hterm \<Rightarrow> hterm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "inst_by_match pat tm th = do { i \<leftarrow> term_match [] pat tm; INSTANTIATE i th }"

definition lemma_instances :: "wctx \<Rightarrow> hterm list \<Rightarrow> hthm list" where
  "lemma_instances cx gs =
     concat (map (\<lambda>g. List.map_filter (\<lambda>(lth, pat). inst_by_match pat g lth) (w_glemmas cx)) gs)"

fun elim_lemmas :: "hthm list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "elim_lemmas [] cur = Some cur"
| "elim_lemmas (lth # ls) cur =
     (case dest_disj (concl cur) of
        None \<Rightarrow> None
      | Some (np, r) \<Rightarrow>
          do { a \<leftarrow> ASSUME np;
               n \<leftarrow> NOT_ELIM a;
               f \<leftarrow> MP n lth;
               c1 \<leftarrow> CONTR r f;
               c2 \<leftarrow> ASSUME r;
               nxt \<leftarrow> DISJ_CASES cur c1 c2;
               elim_lemmas ls nxt })"

definition gen_goal_and_just ::
  "wctx \<Rightarrow> hterm \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> (hterm \<times> (hthm list \<Rightarrow> hthm option))" where
  "gen_goal_and_just cx tm pairs =
     (let gs = map fst pairs;
          cl' = rep_pairs pairs tm;
          lems = lemma_instances cx gs;
          nots = map (\<lambda>l. mk_not (rep_pairs pairs (concl l))) lems;
          goal = foldr mk_disj nots cl'
      in (goal,
          (\<lambda>ths. case ths of
                   [th] \<Rightarrow> do { th1 \<leftarrow> INST pairs th;
                               th2 \<leftarrow> elim_lemmas lems th1;
                               if aconv (concl th2) tm then Some th2 else None }
                 | _ \<Rightarrow> None)))"

section \<open>Generalizing variables apart (4.4.2)\<close>

primrec vars_ord :: "hterm \<Rightarrow> hterm list" where
  "vars_ord (Var n ty) = [Var n ty]"
| "vars_ord (Const n ty) = []"
| "vars_ord (Comb s t) = vars_ord s @ vars_ord t"
| "vars_ord (Abs v b) = filter (\<lambda>x. x \<noteq> v) (vars_ord b)"


definition rec_positions :: "hthm list \<Rightarrow> shell list \<Rightarrow> (string \<times> nat list) list" where
  "rec_positions rules shs =
     (let rs = List.map_filter (\<lambda>th. case strip_conds (concl th) of (_, e) \<Rightarrow> map_option fst (dest_eq e)) rules
      in map (\<lambda>n. (n, remdups (concat (map (\<lambda>l. case strip_comb l of
                                                  (Const m _, args) \<Rightarrow>
                                                    (if m = n then
                                                       List.map_filter (\<lambda>(i, a). if (case strip_comb a of (Const c _, _) \<Rightarrow> is_con_name shs c | _ \<Rightarrow> False) then Some i else None)
                                                         (zip [0..<length args] args)
                                                     else [])
                                                | _ \<Rightarrow> []) rs))))
           (remdups (List.map_filter (\<lambda>l. case strip_comb l of (Const m _, _ # _) \<Rightarrow> Some m | _ \<Rightarrow> None) rs)))"

primrec replace_path :: "nat list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "replace_path [] new t = new"
| "replace_path (i # rest) new t =
     (case strip_comb t of
        (h, args) \<Rightarrow>
          (if i < length args
           then foldl Comb h (take i args @ [replace_path rest new (args ! i)] @ drop (Suc i) args)
           else t))"

primrec apps_n :: "nat \<Rightarrow> nat list \<Rightarrow> hterm \<Rightarrow> (nat list \<times> string \<times> hterm list) list" where
  "apps_n 0 path t = []"
| "apps_n (Suc k) path t =
     (case strip_comb t of
        (Const f _, args) \<Rightarrow>
          (if args = [] then []
           else (path, f, args) #
                concat (map (\<lambda>(i, a). apps_n k (path @ [i]) a) (zip [0..<length args] args)))
      | (_, args) \<Rightarrow> concat (map (\<lambda>(i, a). apps_n k (path @ [i]) a) (zip [0..<length args] args)))"

text \<open>Rebuild a literal from new roots.\<close>

definition lit_with_roots :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm" where
  "lit_with_roots l roots =
     (let a = lit_atom l;
          a' = (case dest_eq a of
                  Some _ \<Rightarrow> (case roots of [x, y] \<Rightarrow> safe_mk_eq x y | _ \<Rightarrow> a)
                | None \<Rightarrow> (case strip_comb a of (h, _) \<Rightarrow> foldl Comb h roots))
      in (case dest_neg l of Some _ \<Rightarrow> mk_not a' | None \<Rightarrow> a'))"

definition h_apart :: "wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> hres \<times> wst" where
  "h_apart cx ind tm st =
     (let ls = disjuncts tm;
          rp = rec_positions (w_rules cx) (w_shells cx);
          rts = concat (map (\<lambda>(li, l). map (\<lambda>(ri, r). (li, ri, r)) (zip [0..<length (lit_roots l)] (lit_roots l)))
                            (zip [0..<length ls] ls));
          occs = concat (map (\<lambda>(li, ri, r). map (\<lambda>(p, f, args). (li, ri, p, f, args)) (apps_n (tm_size r) [] r)) rts);
          props = concat (map (\<lambda>o1.
                    concat (map (\<lambda>o2.
                      (case (o1, o2) of
                         ((li1, ri1, p1, f1, a1), (li2, ri2, p2, f2, a2)) \<Rightarrow>
                           (if f1 = f2 \<and> (li1, ri1, p1) \<noteq> (li2, ri2, p2) then
                              (case map_of rp f1 of
                                 None \<Rightarrow> []
                               | Some rps \<Rightarrow>
                                   concat (map (\<lambda>i. concat (map (\<lambda>j.
                                     (if i \<in> set rps \<and> j \<notin> set rps \<and> i < length a1 \<and> j < length a2
                                         \<and> is_var (a1 ! i) \<and> a1 ! i = a2 ! j
                                      then [(a1 ! i, (li1, ri1, p1 @ [i]), (li2, ri2, p2 @ [j]))] else []))
                                     [0..<length a2])) [0..<length a1]))
                            else []))) occs)) occs)
      in case props of
           [] \<Rightarrow> (HFail, st)
         | (v, (l1, r1, q1), (l2, r2, q2)) # _ \<Rightarrow>
             (let v' = variant (frees tm) (Var ''n'' (type_of v));
                  upd = (\<lambda>li ri r.
                           (if (li, ri) = (l1, r1) then replace_path q1 v' r else r))
                  ; roots_new = (\<lambda>li l. map (\<lambda>ri. let r = lit_roots l ! ri in
                                                  let r1' = (if (li, ri) = (l1, r1) then replace_path q1 v' r else r) in
                                                  if (li, ri) = (l2, r2) then replace_path q2 v' (if (li, ri) = (l1, r1) then r1' else r) else r1')
                                  [0..<length (lit_roots l)])
                  ; ls' = map (\<lambda>(li, l). lit_with_roots l (roots_new li l)) (zip [0..<length ls] ls);
                  goal = mk_clause ls';
                  cnt = (\<lambda>t. length (filter (\<lambda>u. u = v) (vars_ord t)));
                  side_ok = (\<lambda>bef aft.
                               aft = v' \<or> (let nb = cnt bef; na = cnt aft in na < nb \<and> 1 \<le> na));
                  lit_ok = (\<lambda>li l. (case dest_eq (lit_atom l) of
                                      None \<Rightarrow> True
                                    | Some _ \<Rightarrow>
                                        list_all (\<lambda>ri. side_ok (lit_roots l ! ri) (roots_new li l ! ri))
                                                 (filter (\<lambda>ri. roots_new li l ! ri \<noteq> lit_roots l ! ri)
                                                         [0..<length (lit_roots l)]))
                                   \<and> (case dest_eq (lit_atom l) of
                                        None \<Rightarrow> True
                                      | Some _ \<Rightarrow> (let ch = filter (\<lambda>ri. roots_new li l ! ri \<noteq> lit_roots l ! ri) [0..<length (lit_roots l)]
                                                  in ch = [] \<or> length ch = length (lit_roots l))));
                  useful = list_all (\<lambda>(li, l). lit_ok li l) (zip [0..<length ls] ls)
              in if \<not> useful then (HFail, st) else
                 case unsafe_to_generalize cx goal st of
                   (True, st1) \<Rightarrow> (HFail, st1\<lparr> w_overs := w_overs st1 + 1 \<rparr>)
                 | (False, st1) \<Rightarrow>
                     (HSub [goal] (\<lambda>ths. case ths of
                                           [th] \<Rightarrow> (do { t1 \<leftarrow> INST [(v, v')] th;
                                                        if aconv (concl t1) tm then Some t1 else None })
                                         | _ \<Rightarrow> None),
                      st1\<lparr> w_gens := w_gens st1 + 1 \<rparr>)))"


section \<open>Induction (3.1, 3.2)\<close>

definition shell_for_var :: "shell list \<Rightarrow> hterm \<Rightarrow> (shell \<times> (hol_type \<times> hol_type) list) option" where
  "shell_for_var shs x =
     (case List.map_filter (\<lambda>sh. map_option (\<lambda>e. (sh, e)) (type_match (sh_ty sh) (type_of x) [])) shs of
        [] \<Rightarrow> None
      | r # _ \<Rightarrow> Some r)"

definition lit_app_roots :: "hterm \<Rightarrow> hterm list" where
  "lit_app_roots l =
     (let a = lit_atom l in
      case dest_eq a of Some (x, y) \<Rightarrow> [x, y] | None \<Rightarrow> [a])"

definition ind_score :: "(string \<times> nat list) list \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> nat" where
  "ind_score rp ls v =
     length (filter (\<lambda>(p, f, args). case map_of rp f of
                                      None \<Rightarrow> False
                                    | Some rps \<Rightarrow> list_ex (\<lambda>i. i < length args \<and> args ! i = v) rps)
                    (concat (map (\<lambda>r. apps_n (tm_size r) [] r) (concat (map lit_app_roots ls)))))"

section \<open>Aderhold's common subterm generalization (4.4.1)\<close>

text \<open>Step 1, generalizable subterms: as in Boyer-Moore (neither a variable, nor an explicit value
  template, nor an application of accessor functions) and in addition free of constructors
  (@{text "gen_ok cx True"}).

  Step 2, proposals: sets of generalizable subterms that occur in a recursive position of a
  function, or that form one of the sides of an equation.  A proposal is suitable for the clause
  if each of its terms occurs at least twice in it and satisfies the equation criterion: in every
  equation in which it occurs it occurs on both sides, or at least twice on one side.

  Step 3, evaluation: the proposals are ordered by the induction test (induction is possible on
  each generalized variable), by how often they were proposed, and by the number of occurrences
  of their terms; only the single best proposal is applied.  Terms that were generalized before
  are not proposed again, and the counterexample checker rejects over-generalizations in
  @{text h_gen}.\<close>

definition eq_crit :: "hterm \<Rightarrow> hterm list \<Rightarrow> bool" where
  "eq_crit g ls =
     list_all (\<lambda>l. case dest_eq (lit_atom l) of
                     Some (x, y) \<Rightarrow> (g \<in> set (subs x) \<or> g \<in> set (subs y)) \<longrightarrow>
                                   (g \<in> set (subs x) \<and> g \<in> set (subs y)
                                    \<or> occ_count g (subs x) \<ge> 2 \<or> occ_count g (subs y) \<ge> 2)
                   | None \<Rightarrow> True) ls"

definition clause_nodes :: "hterm list \<Rightarrow> hterm list" where
  "clause_nodes ls = concat (map (\<lambda>l. lit_atom l # concat (map subs (lit_roots l))) ls)"

definition node_proposals :: "wctx \<Rightarrow> (string \<times> nat list) list \<Rightarrow> hterm \<Rightarrow> hterm list list" where
  "node_proposals cx rp u =
     (case strip_comb u of
        (Const n _, args) \<Rightarrow>
          (case map_of rp n of
             Some rps \<Rightarrow>
               (let p = dedup_aconv (filter (gen_ok cx True)
                          (List.map_filter (\<lambda>i. if i < length args then Some (args ! i) else None) rps))
                in if p = [] then [] else [p])
           | None \<Rightarrow> [])
      | _ \<Rightarrow> [])"

definition side_proposals :: "wctx \<Rightarrow> hterm \<Rightarrow> hterm list list" where
  "side_proposals cx l =
     (case dest_eq (lit_atom l) of
        Some (x, y) \<Rightarrow> map (\<lambda>t. [t]) (filter (gen_ok cx True) [x, y])
      | None \<Rightarrow> [])"

definition prop_eq :: "hterm list \<Rightarrow> hterm list \<Rightarrow> bool" where
  "prop_eq p q = (length p = length q \<and> list_all (\<lambda>a. list_ex (aconv a) q) p)"

fun add_prop :: "hterm list \<Rightarrow> (hterm list \<times> nat) list \<Rightarrow> (hterm list \<times> nat) list" where
  "add_prop p [] = [(p, 1)]"
| "add_prop p ((q, n) # r) = (if prop_eq p q then (q, n + 1) # r else (q, n) # add_prop p r)"

definition proposals :: "wctx \<Rightarrow> (string \<times> nat list) list \<Rightarrow> hterm list \<Rightarrow> (hterm list \<times> nat) list" where
  "proposals cx rp ls =
     foldl (\<lambda>acc p. add_prop p acc) []
       (concat (map (node_proposals cx rp) (clause_nodes ls)) @ concat (map (side_proposals cx) ls))"

definition ad_suitable :: "hterm list \<Rightarrow> hterm list \<Rightarrow> bool" where
  "ad_suitable ls p =
     (let nodes = concat (map subs (concat (map lit_roots ls)))
      in list_all (\<lambda>t. occ_count t nodes \<ge> 2 \<and> eq_crit t ls) p)"

definition ind_possible :: "wctx \<Rightarrow> (string \<times> nat list) list \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> bool" where
  "ind_possible cx rp ls v =
     (shell_for_var (w_shells cx) v \<noteq> None \<and> ind_score rp ls v > 0)"

definition ad_key :: "wctx \<Rightarrow> (string \<times> nat list) list \<Rightarrow> hterm \<Rightarrow> hterm list \<times> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "ad_key cx rp tm pn =
     (let p = fst pn;
          pairs = fresh_vars (frees tm) p;
          ls' = disjuncts (rep_pairs pairs tm);
          nodes = concat (map subs (concat (map lit_roots (disjuncts tm))))
      in ((if list_all (\<lambda>(g, v). ind_possible cx rp ls' v) pairs then 1 else 0),
          snd pn,
          sum_list (map (\<lambda>t. occ_count t nodes) p)))"

definition key_better :: "nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat \<Rightarrow> bool" where
  "key_better k1 k2 =
     (case (k1, k2) of
        ((a1, b1, c1), (a2, b2, c2)) \<Rightarrow> a1 > a2 \<or> (a1 = a2 \<and> (b1 > b2 \<or> (b1 = b2 \<and> c1 > c2))))"

definition ad_select :: "wctx \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "ad_select cx ls tm gened =
     (let rp = rec_positions (w_rules cx) (w_shells cx);
          props = filter (\<lambda>pn. ad_suitable ls (fst pn)
                               \<and> \<not> list_ex (\<lambda>t. list_ex (aconv t) gened) (fst pn))
                         (proposals cx rp ls)
      in case props of
           [] \<Rightarrow> []
         | pn # rest \<Rightarrow>
             fst (foldl (\<lambda>b c. if key_better (ad_key cx rp tm c) (ad_key cx rp tm b) then c else b) pn rest))"

definition h_gen :: "bool \<Rightarrow> wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> hres \<times> wst" where
  "h_gen ad cx ind tm st =
     (let ls = disjuncts tm;
          sel = (if ad then ad_select cx ls tm (w_gened st)
                 else filter (\<lambda>g. \<not> list_ex (aconv g) (w_gened st)) (gen_cands cx ls))
      in if sel = [] then (HFail, st)
         else
           (let pairs = fresh_vars (frees tm) sel;
                (goal, just) = gen_goal_and_just cx tm pairs
            in case unsafe_to_generalize cx goal st of
                 (True, st1) \<Rightarrow> (HFail, st1\<lparr> w_overs := w_overs st1 + 1, w_gened := sel @ w_gened st1 \<rparr>)
               | (False, st1) \<Rightarrow>
                   (HSub [goal] just,
                    st1\<lparr> w_gens := w_gens st1 + 1, w_gened := sel @ w_gened st1 \<rparr>)))"


definition choose_ind_var :: "wctx \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "choose_ind_var cx tm =
     (let ls = disjuncts tm;
          rp = rec_positions (w_rules cx) (w_shells cx);
          vs = filter (\<lambda>v. shell_for_var (w_shells cx) v \<noteq> None) (dedup_aconv (vars_ord tm))
      in case vs of
           [] \<Rightarrow> None
         | v0 # rest \<Rightarrow>
             Some (foldl (\<lambda>b v. if ind_score rp ls v > ind_score rp ls b then v else b) v0 rest))"

fun strip_foralls_n :: "nat \<Rightarrow> hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_foralls_n 0 tm = ([], tm)"
| "strip_foralls_n (Suc k) tm =
     (case dest_forall tm of
        Some (v, b) \<Rightarrow> (case strip_foralls_n k b of (vs, bd) \<Rightarrow> (v # vs, bd))
      | None \<Rightarrow> ([], tm))"

definition strip_foralls :: "hterm \<Rightarrow> hterm list \<times> hterm" where
  "strip_foralls tm = strip_foralls_n (tm_size tm) tm"

definition fresh_list :: "hterm list \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "fresh_list avoid vs =
     snd (foldl (\<lambda>(av, acc) v. (let v' = variant av v in (v' # av, acc @ [v']))) (avoid, []) vs)"

text \<open>Induction with the shell's induction theorem: the base cases and step cases are the
  conjuncts of its antecedent after instantiating the predicate with the abstracted clause
  and beta-reducing.  Step cases (those with an induction hypothesis) are flagged, so that
  the equality heuristic may cross-fertilize.\<close>

definition induct_prep ::
  "wctx \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> ((hterm \<times> bool) list \<times> (hthm list \<Rightarrow> hthm option)) option" where
  "induct_prep cx tm x =
     do { (sh, tye) \<leftarrow> shell_for_var (w_shells cx) x;
          th0 \<leftarrow> INST_TYPE tye (sh_induct sh);
          th1 \<leftarrow> SPEC (Abs x tm) th0;
          th2 \<leftarrow> CONV_RULE (REDEPTH_CONV BETA_CONV) th1;
          (a, _) \<leftarrow> dest_imp (concl th2);
          let cases = conjuncts a;
          let avoid = frees tm;
          let info = map (\<lambda>c. (case strip_foralls c of
                                 (vs, _) \<Rightarrow> let vs' = fresh_list avoid vs in (c, vs'))) cases;
          goals \<leftarrow> those (map (\<lambda>(c, vs'). do { ac \<leftarrow> ASSUME c;
                                               sp \<leftarrow> SPECL vs' ac;
                                               Some (concl sp) }) info);
          Some (map (\<lambda>g. (g, dest_imp g \<noteq> None)) goals,
                (\<lambda>ths. do { gens \<leftarrow> those (map (\<lambda>((c, vs'), th). GENL vs' th) (zip info ths));
                            cj \<leftarrow> build_conj a gens;
                            m \<leftarrow> MP th2 cj;
                            SPEC x m })) }"

section \<open>The waterfall\<close>

definition run_heur :: "heur \<Rightarrow> wctx \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> hres \<times> wst" where
  "run_heur h cx ind tm st =
     (case h of
        H_Clausal \<Rightarrow> (h_clausal cx ind tm, st)
      | H_Taut \<Rightarrow> (h_taut cx ind tm, st)
      | H_Setify \<Rightarrow> (h_setify cx ind tm, st)
      | H_Subst \<Rightarrow> (h_subst cx ind tm, st)
      | H_Simp \<Rightarrow> (h_simp cx ind tm, st)
      | H_Equal \<Rightarrow> (h_equal cx ind tm, st)
      | H_GenBM \<Rightarrow> h_gen False cx ind tm st
      | H_GenAd \<Rightarrow> h_gen True cx ind tm st
      | H_GenApart \<Rightarrow> h_apart cx ind tm st
      | H_Irrel \<Rightarrow> (h_irrel cx ind tm, st))"

text \<open>The warehouse filter: a heuristic that already succeeded on the same clause in this
  waterfall is skipped, to avoid loops.\<close>

primrec run_pipe ::
  "heur list \<Rightarrow> wctx \<Rightarrow> (hterm \<times> heur) list \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> (heur \<times> hres) option \<times> wst" where
  "run_pipe [] cx wh ind tm st = (None, st)"
| "run_pipe (h # hs) cx wh ind tm st =
     (if list_ex (\<lambda>p. aconv (fst p) tm \<and> snd p = h) wh then run_pipe hs cx wh ind tm st
      else
        (case run_heur h cx ind tm st of
           (HFail, st') \<Rightarrow> run_pipe hs cx wh ind tm st'
         | (r, st') \<Rightarrow> (Some (h, r), st')))"

primrec var_depth_n :: "nat \<Rightarrow> hterm \<Rightarrow> nat" where
  "var_depth_n 0 t = 0"
| "var_depth_n (Suc k) t =
     (case strip_comb t of
        (_, args) \<Rightarrow> foldl max 0 (map (\<lambda>a. if frees a = [] then 0 else Suc (var_depth_n k a)) args))"

definition clause_depth :: "hterm \<Rightarrow> nat" where
  "clause_depth tm =
     foldl max 0 (map (\<lambda>r. var_depth_n (tm_size r) r) (concat (map lit_roots (disjuncts tm))))"

text \<open>The terms generalized so far (the warehouse of generalizations, which prevents generalizing
  the same term again after induction has reintroduced it) are scoped to the subtree of the
  proof below the generalization step: sibling subgoals do not see each other's entries.\<close>

definition pour_all ::
  "((hterm \<times> bool) \<Rightarrow> wst \<Rightarrow> hthm option \<times> wst) \<Rightarrow> (hterm \<times> bool) list \<Rightarrow> wst \<Rightarrow> hthm list option \<times> wst" where
  "pour_all f gs st =
     (let g0 = w_gened st in
      case foldl (\<lambda>(acc, s) g.
                    case acc of
                      None \<Rightarrow> (None, s)
                    | Some ths \<Rightarrow> (case f g (s\<lparr> w_gened := g0 \<rparr>) of
                                    (Some th, s') \<Rightarrow> (Some (ths @ [th]), s')
                                  | (None, s') \<Rightarrow> (None, s')))
                 (Some [], st) gs
      of (r, s) \<Rightarrow> (r, s\<lparr> w_gened := g0 \<rparr>))"

primrec pour ::
  "nat \<Rightarrow> wctx \<Rightarrow> (hterm \<times> heur) list \<Rightarrow> hterm list \<Rightarrow> bool \<Rightarrow> hterm \<Rightarrow> wst \<Rightarrow> hthm option \<times> wst" where
  "pour 0 cx wh ih ind tm st = (None, add_note ''  (out of fuel)'' st)"
| "pour (Suc n) cx wh ih ind tm st =
     (let st1 = add_note (pp_tm tm) (st\<lparr> w_steps := w_steps st + 1 \<rparr>) in
      if clause_depth tm > w_maxdepth cx then (None, add_note ''-> maximum depth exceeded'' st1)
      else
        (case run_pipe (w_order cx) cx wh ind tm st1 of
           (Some (h, res), st2) \<Rightarrow>
             (case res of
                HProved th \<Rightarrow> (Some th, add_note (''-> '' @ pp_heur h @ '' (proved)'') st2)
              | HDisproved \<Rightarrow> (None, add_note (''-> '' @ pp_heur h @ '' (disproved)'') st2)
              | HFail \<Rightarrow> (None, st2)
              | HSub gs just \<Rightarrow>
                  (case pour_all (\<lambda>p s. pour n cx ((tm, h) # wh) ih ind (fst p) s)
                                 (map (\<lambda>g. (g, ind)) gs)
                                 (add_note (''-> '' @ pp_heur h) st2) of
                     (Some ths, st3) \<Rightarrow> (just ths, st3)
                   | (None, st3) \<Rightarrow> (None, st3)))
         | (None, st2) \<Rightarrow>
             (if list_ex (aconv tm) ih then (None, add_note ''-> induction already applied'' st2)
              else
                (case choose_ind_var cx tm of
                   None \<Rightarrow> (None, add_note ''-> no induction variable'' st2)
                 | Some x \<Rightarrow>
                     (case induct_prep cx tm x of
                        None \<Rightarrow> (None, add_note ''-> induction failed'' st2)
                      | Some (gs, just) \<Rightarrow>
                          (case pour_all (\<lambda>p s. pour n cx [] (tm # ih) (snd p) (fst p) s) gs
                                 (add_note (''Doing induction on: '' @ pp_tm x) (st2\<lparr> w_inds := w_inds st2 + 1 \<rparr>)) of
                             (Some ths, st3) \<Rightarrow> (just ths, st3)
                           | (None, st3) \<Rightarrow> (None, st3)))))))"

definition bm_prove :: "wctx \<Rightarrow> nat \<Rightarrow> hterm \<Rightarrow> hthm option \<times> wst" where
  "bm_prove cx fuel goal =
     (case strip_foralls goal of
        (vs, bd) \<Rightarrow>
          (case pour fuel cx [] [] False bd init_wst of
             (Some th, st) \<Rightarrow> (GENL vs th, st)
           | (None, st) \<Rightarrow> (None, st)))"

definition bm_order :: "heur list" where
  "bm_order = [H_Clausal, H_Subst, H_Simp, H_Equal, H_GenBM, H_Irrel]"

definition bme_order :: "heur list" where
  "bme_order = [H_Clausal, H_Taut, H_Subst, H_Simp, H_Setify, H_Equal, H_GenBM, H_Irrel]"

definition bmf_order :: "heur list" where
  "bmf_order = [H_Clausal, H_Taut, H_Subst, H_Simp, H_Setify, H_Equal, H_GenAd, H_GenApart, H_Irrel]"

section \<open>Peano arithmetic: a shell for the natural numbers\<close>

definition num_ty :: hol_type where "num_ty = Tyapp ''num'' []"
definition num1 :: "hol_type" where "num1 = fun_ty num_ty num_ty"
definition num2 :: "hol_type" where "num2 = fun_ty num_ty (fun_ty num_ty num_ty)"
definition zero_c :: hterm where "zero_c = Const ''0'' num_ty"
definition suc_c :: hterm where "suc_c = Const ''SUC'' num1"
definition pre_c :: hterm where "pre_c = Const ''PRE'' num1"
definition add_c :: hterm where "add_c = Const ''+'' num2"
definition mul_c :: hterm where "mul_c = Const ''*'' num2"

definition numb2 :: "hol_type" where "numb2 = fun_ty num_ty (fun_ty num_ty bool_ty)"
definition le_c :: hterm where "le_c = Const ''<='' numb2"
definition lt_c :: hterm where "lt_c = Const ''<'' numb2"

definition exp_c :: hterm where "exp_c = Const ''EXP'' num2"
definition sub_c :: hterm where "sub_c = Const ''-'' num2"
definition even_c :: hterm where "even_c = Const ''EVEN'' (fun_ty num_ty bool_ty)"

definition mk_suc :: "hterm \<Rightarrow> hterm" where "mk_suc t = Comb suc_c t"
definition mk_pre :: "hterm \<Rightarrow> hterm" where "mk_pre t = Comb pre_c t"
definition mk_add :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_add a b = Comb (Comb add_c a) b"
definition mk_mul :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_mul a b = Comb (Comb mul_c a) b"

definition mk_exp :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_exp a b = Comb (Comb exp_c a) b"
definition mk_sub :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_sub a b = Comb (Comb sub_c a) b"
definition mk_even :: "hterm \<Rightarrow> hterm" where "mk_even a = Comb even_c a"

definition nm :: "string \<Rightarrow> hterm" where "nm s = Var s num_ty"

definition mk_le :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_le a b = Comb (Comb le_c a) b"
definition mk_lt :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_lt a b = Comb (Comb lt_c a) b"

definition le_ax_tm :: hterm where
  "le_ax_tm =
     mk_conj (mk_forall (nm ''m'') (safe_mk_eq (mk_le (nm ''m'') zero_c) (safe_mk_eq (nm ''m'') zero_c)))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_le (nm ''m'') (mk_suc (nm ''n'')))
                            (mk_disj (safe_mk_eq (nm ''m'') (mk_suc (nm ''n''))) (mk_le (nm ''m'') (nm ''n''))))))"

definition lt_ax_tm :: hterm where
  "lt_ax_tm =
     mk_conj (mk_forall (nm ''m'') (safe_mk_eq (mk_lt (nm ''m'') zero_c) F_tm))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_lt (nm ''m'') (mk_suc (nm ''n'')))
                            (mk_disj (safe_mk_eq (nm ''m'') (nm ''n'')) (mk_lt (nm ''m'') (nm ''n''))))))"

definition ind_ax_tm :: hterm where
  "ind_ax_tm =
     (let P = Var ''P'' (fun_ty num_ty bool_ty); n = nm ''n'' in
      mk_forall P
        (mk_imp (mk_conj (Comb P zero_c)
                         (mk_forall n (mk_imp (Comb P n) (Comb P (mk_suc n)))))
                (mk_forall n (Comb P n))))"

definition distinct_ax_tm :: hterm where
  "distinct_ax_tm = mk_forall (nm ''n'') (mk_not (safe_mk_eq (mk_suc (nm ''n'')) zero_c))"

definition oneone_ax_tm :: hterm where
  "oneone_ax_tm =
     mk_forall (nm ''m'') (mk_forall (nm ''n'')
       (safe_mk_eq (safe_mk_eq (mk_suc (nm ''m'')) (mk_suc (nm ''n''))) (safe_mk_eq (nm ''m'') (nm ''n''))))"

definition pre_ax_tm :: hterm where
  "pre_ax_tm = mk_conj (safe_mk_eq (mk_pre zero_c) zero_c)
                       (mk_forall (nm ''n'') (safe_mk_eq (mk_pre (mk_suc (nm ''n''))) (nm ''n'')))"

definition add_ax_tm :: hterm where
  "add_ax_tm =
     mk_conj (mk_forall (nm ''n'') (safe_mk_eq (mk_add zero_c (nm ''n'')) (nm ''n'')))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_add (mk_suc (nm ''m'')) (nm ''n'')) (mk_suc (mk_add (nm ''m'') (nm ''n''))))))"

definition mul_ax_tm :: hterm where
  "mul_ax_tm =
     mk_conj (mk_forall (nm ''n'') (safe_mk_eq (mk_mul zero_c (nm ''n'')) zero_c))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_mul (mk_suc (nm ''m'')) (nm ''n''))
                            (mk_add (mk_mul (nm ''m'') (nm ''n'')) (nm ''n'')))))"

text \<open>Further primitive recursive functions of HOL Light's arithmetic: exponentiation, truncated
  subtraction (recursion on the second argument) and @{text EVEN}.\<close>

definition exp_ax_tm :: hterm where
  "exp_ax_tm =
     mk_conj (mk_forall (nm ''m'') (safe_mk_eq (mk_exp (nm ''m'') zero_c) (mk_suc zero_c)))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_exp (nm ''m'') (mk_suc (nm ''n'')))
                            (mk_mul (nm ''m'') (mk_exp (nm ''m'') (nm ''n''))))))"

definition sub_ax_tm :: hterm where
  "sub_ax_tm =
     mk_conj (mk_forall (nm ''m'') (safe_mk_eq (mk_sub (nm ''m'') zero_c) (nm ''m'')))
             (mk_forall (nm ''m'') (mk_forall (nm ''n'')
                (safe_mk_eq (mk_sub (nm ''m'') (mk_suc (nm ''n'')))
                            (mk_pre (mk_sub (nm ''m'') (nm ''n''))))))"

definition even_ax_tm :: hterm where
  "even_ax_tm =
     mk_conj (safe_mk_eq (mk_even zero_c) T_tm)
             (mk_forall (nm ''n'') (safe_mk_eq (mk_even (mk_suc (nm ''n''))) (mk_not (mk_even (nm ''n'')))))"

text \<open>Build the theory of Peano arithmetic in the kernel: one new type, five constants and the
  Peano axioms (including the defining equations of @{text "+"} and @{text "*"}).\<close>

definition peano_init :: "(kstate \<times> hthm list) option" where
  "peano_init =
     do { k1 \<leftarrow> new_type bool_kstate (''num'', 0);
          k2 \<leftarrow> new_constant k1 (''0'', num_ty);
          k3 \<leftarrow> new_constant k2 (''SUC'', num1);
          k4 \<leftarrow> new_constant k3 (''PRE'', num1);
          k5 \<leftarrow> new_constant k4 (''+'', num2);
          k6a \<leftarrow> new_constant k5 (''*'', num2);
          k6b \<leftarrow> new_constant k6a (''<='', numb2);
          k6c \<leftarrow> new_constant k6b (''<'', numb2);
          k6d \<leftarrow> new_constant k6c (''EXP'', num2);
          k6e \<leftarrow> new_constant k6d (''-'', num2);
          k6 \<leftarrow> new_constant k6e (''EVEN'', fun_ty num_ty bool_ty);
          (k7, t1) \<leftarrow> new_axiom k6 ind_ax_tm;
          (k8, t2) \<leftarrow> new_axiom k7 distinct_ax_tm;
          (k9, t3) \<leftarrow> new_axiom k8 oneone_ax_tm;
          (k10, t4) \<leftarrow> new_axiom k9 pre_ax_tm;
          (k11, t5) \<leftarrow> new_axiom k10 add_ax_tm;
          (k12, t6) \<leftarrow> new_axiom k11 mul_ax_tm;
          (k13, t7) \<leftarrow> new_axiom k12 le_ax_tm;
          (k14, t8) \<leftarrow> new_axiom k13 lt_ax_tm;
          (k15, t9) \<leftarrow> new_axiom k14 exp_ax_tm;
          (k16, t10) \<leftarrow> new_axiom k15 sub_ax_tm;
          (k17, t11) \<leftarrow> new_axiom k16 even_ax_tm;
          Some (k17, [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]) }"

definition peano_thm :: "nat \<Rightarrow> hthm" where "peano_thm i = snd (the peano_init) ! i"

definition nat_shell :: shell where
  "nat_shell =
     \<lparr> sh_name = ''num'', sh_ty = num_ty, sh_bottoms = [zero_c], sh_cons = [suc_c],
       sh_accs = [pre_c], sh_type_axiom = None, sh_induct = peano_thm 0, sh_cases = None,
       sh_distinct = [peano_thm 1], sh_oneone = [peano_thm 2], sh_accdefs = [peano_thm 3] \<rparr>"

definition nat_rules :: "hthm list" where
  "nat_rules = mk_rewrites_l (sh_distinct nat_shell @ sh_oneone nat_shell @ sh_accdefs nat_shell
                              @ [peano_thm 4, peano_thm 5, peano_thm 6, peano_thm 7,
                                 peano_thm 8, peano_thm 9, peano_thm 10])"

definition nat_ctx :: "heur list \<Rightarrow> wctx" where
  "nat_ctx order =
     \<lparr> w_shells = [nat_shell], w_rules = nat_rules, w_glemmas = [], w_order = order,
       w_maxdepth = 12, w_ncex = 5 \<rparr>"


section \<open>A second shell: polymorphic lists\<close>

definition lty :: hol_type where "lty = Tyapp ''list'' [aty]"
definition nil_c :: hterm where "nil_c = Const ''NIL'' lty"
definition cons_c :: hterm where "cons_c = Const ''CONS'' (fun_ty aty (fun_ty lty lty))"
definition hd_c :: hterm where "hd_c = Const ''HD'' (fun_ty lty aty)"
definition tl_c :: hterm where "tl_c = Const ''TL'' (fun_ty lty lty)"
definition append_c :: hterm where "append_c = Const ''APPEND'' (fun_ty lty (fun_ty lty lty))"
definition rev_c :: hterm where "rev_c = Const ''REVERSE'' (fun_ty lty lty)"
definition len_c :: hterm where "len_c = Const ''LENGTH'' (fun_ty lty num_ty)"

definition lv :: "string \<Rightarrow> hterm" where "lv s = Var s lty"
definition av :: "string \<Rightarrow> hterm" where "av s = Var s aty"
definition mk_cons :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_cons a l = Comb (Comb cons_c a) l"
definition mk_append :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where "mk_append a b = Comb (Comb append_c a) b"
definition mk_rev :: "hterm \<Rightarrow> hterm" where "mk_rev l = Comb rev_c l"
definition mk_len :: "hterm \<Rightarrow> hterm" where "mk_len l = Comb len_c l"

definition list_ind_tm :: hterm where
  "list_ind_tm =
     (let P = Var ''P'' (fun_ty lty bool_ty) in
      mk_forall P
        (mk_imp (mk_conj (Comb P nil_c)
                         (mk_foralls [av ''a'', lv ''l''] (mk_imp (Comb P (lv ''l'')) (Comb P (mk_cons (av ''a'') (lv ''l''))))))
                (mk_forall (lv ''l'') (Comb P (lv ''l'')))))"

definition list_distinct_tm :: hterm where
  "list_distinct_tm = mk_foralls [av ''a'', lv ''l''] (mk_not (safe_mk_eq (mk_cons (av ''a'') (lv ''l'')) nil_c))"

definition list_oneone_tm :: hterm where
  "list_oneone_tm =
     mk_foralls [av ''a'', lv ''l'', av ''b'', lv ''m'']
       (safe_mk_eq (safe_mk_eq (mk_cons (av ''a'') (lv ''l'')) (mk_cons (av ''b'') (lv ''m'')))
                   (mk_conj (safe_mk_eq (av ''a'') (av ''b'')) (safe_mk_eq (lv ''l'') (lv ''m''))))"

definition list_acc_tm :: hterm where
  "list_acc_tm =
     mk_conj (mk_foralls [av ''a'', lv ''l''] (safe_mk_eq (Comb hd_c (mk_cons (av ''a'') (lv ''l''))) (av ''a'')))
             (mk_foralls [av ''a'', lv ''l''] (safe_mk_eq (Comb tl_c (mk_cons (av ''a'') (lv ''l''))) (lv ''l'')))"

definition list_append_tm :: hterm where
  "list_append_tm =
     mk_conj (mk_forall (lv ''l'') (safe_mk_eq (mk_append nil_c (lv ''l'')) (lv ''l'')))
             (mk_foralls [av ''a'', lv ''l1'', lv ''l2'']
                (safe_mk_eq (mk_append (mk_cons (av ''a'') (lv ''l1'')) (lv ''l2''))
                            (mk_cons (av ''a'') (mk_append (lv ''l1'') (lv ''l2'')))))"

definition list_rev_tm :: hterm where
  "list_rev_tm =
     mk_conj (safe_mk_eq (mk_rev nil_c) nil_c)
             (mk_foralls [av ''a'', lv ''l'']
                (safe_mk_eq (mk_rev (mk_cons (av ''a'') (lv ''l'')))
                            (mk_append (mk_rev (lv ''l'')) (mk_cons (av ''a'') nil_c))))"

definition list_len_tm :: hterm where
  "list_len_tm =
     mk_conj (safe_mk_eq (mk_len nil_c) zero_c)
             (mk_foralls [av ''a'', lv ''l''] (safe_mk_eq (mk_len (mk_cons (av ''a'') (lv ''l''))) (mk_suc (mk_len (lv ''l'')))))"

definition list_init :: "(kstate \<times> hthm list) option" where
  "list_init =
     do { (k0, _) \<leftarrow> peano_init;
          k1 \<leftarrow> new_type k0 (''list'', 1);
          k2 \<leftarrow> new_constant k1 (''NIL'', lty);
          k3 \<leftarrow> new_constant k2 (''CONS'', fun_ty aty (fun_ty lty lty));
          k4 \<leftarrow> new_constant k3 (''HD'', fun_ty lty aty);
          k5 \<leftarrow> new_constant k4 (''TL'', fun_ty lty lty);
          k6 \<leftarrow> new_constant k5 (''APPEND'', fun_ty lty (fun_ty lty lty));
          k7 \<leftarrow> new_constant k6 (''REVERSE'', fun_ty lty lty);
          k8 \<leftarrow> new_constant k7 (''LENGTH'', fun_ty lty num_ty);
          (k9, t1) \<leftarrow> new_axiom k8 list_ind_tm;
          (k10, t2) \<leftarrow> new_axiom k9 list_distinct_tm;
          (k11, t3) \<leftarrow> new_axiom k10 list_oneone_tm;
          (k12, t4) \<leftarrow> new_axiom k11 list_acc_tm;
          (k13, t5) \<leftarrow> new_axiom k12 list_append_tm;
          (k14, t6) \<leftarrow> new_axiom k13 list_rev_tm;
          (k15, t7) \<leftarrow> new_axiom k14 list_len_tm;
          Some (k15, [t1, t2, t3, t4, t5, t6, t7]) }"

definition list_thm :: "nat \<Rightarrow> hthm" where "list_thm i = snd (the list_init) ! i"

definition list_shell :: shell where
  "list_shell =
     \<lparr> sh_name = ''list'', sh_ty = lty, sh_bottoms = [nil_c], sh_cons = [cons_c],
       sh_accs = [hd_c, tl_c], sh_type_axiom = None, sh_induct = list_thm 0, sh_cases = None,
       sh_distinct = [list_thm 1], sh_oneone = [list_thm 2], sh_accdefs = [list_thm 3] \<rparr>"

definition list_rules :: "hthm list" where
  "list_rules = mk_rewrites_l (sh_distinct list_shell @ sh_oneone list_shell @ sh_accdefs list_shell
                               @ [list_thm 4, list_thm 5, list_thm 6])"

definition list_ctx :: "heur list \<Rightarrow> wctx" where
  "list_ctx order =
     \<lparr> w_shells = [nat_shell, list_shell], w_rules = nat_rules @ list_rules, w_glemmas = [],
       w_order = order, w_maxdepth = 12, w_ncex = 5 \<rparr>"


section \<open>Examples\<close>

text \<open>Every example below is checked by evaluation: the waterfall returns a kernel theorem
  without hypotheses whose conclusion is the goal.  Names follow the paper's evaluation
  (Table 3): the numbers of steps, inductions and generalizations are recorded in the state.\<close>

definition proves :: "wctx \<Rightarrow> nat \<Rightarrow> hterm \<Rightarrow> bool" where
  "proves cx fuel goal =
     (case bm_prove cx fuel goal of
        (Some th, _) \<Rightarrow> hyp th = [] \<and> aconv (concl th) goal
      | (None, _) \<Rightarrow> False)"

definition vm :: hterm where "vm = nm ''m''"
definition vn :: hterm where "vn = nm ''n''"
definition vk :: hterm where "vk = nm ''p''"

definition g_add_zero :: hterm where
  "g_add_zero = mk_forall vm (safe_mk_eq (mk_add vm zero_c) vm)"
definition g_add_assoc :: hterm where
  "g_add_assoc = mk_foralls [vm, vn, vk] (safe_mk_eq (mk_add vm (mk_add vn vk)) (mk_add (mk_add vm vn) vk))"
definition g_suc_add_one :: hterm where
  "g_suc_add_one = mk_forall vm (safe_mk_eq (mk_suc vm) (mk_add vm (mk_suc zero_c)))"
definition g_add_suc :: hterm where
  "g_add_suc = mk_foralls [vm, vn] (safe_mk_eq (mk_add vm (mk_suc vn)) (mk_suc (mk_add vm vn)))"
definition g_add_comm :: hterm where
  "g_add_comm = mk_foralls [vm, vn] (safe_mk_eq (mk_add vm vn) (mk_add vn vm))"
definition g_mul_zero :: hterm where
  "g_mul_zero = mk_forall vm (safe_mk_eq (mk_mul vm zero_c) zero_c)"
definition g_mul_comm :: hterm where
  "g_mul_comm = mk_foralls [vm, vn] (safe_mk_eq (mk_mul vm vn) (mk_mul vn vm))"
definition g_distrib :: hterm where
  "g_distrib = mk_foralls [vm, vn, vk]
      (safe_mk_eq (mk_mul vm (mk_add vn vk)) (mk_add (mk_mul vm vn) (mk_mul vm vk)))"
definition g_mul_assoc :: hterm where
  "g_mul_assoc = mk_foralls [vm, vn, vk]
      (safe_mk_eq (mk_mul (mk_mul vm vn) vk) (mk_mul vm (mk_mul vn vk)))"
definition g_add_cancel :: hterm where
  "g_add_cancel = mk_foralls [vm, vn, vk]
      (safe_mk_eq (safe_mk_eq (mk_add vm vn) (mk_add vm vk)) (safe_mk_eq vn vk))"
definition g_le_suc_lt :: hterm where
  "g_le_suc_lt = mk_foralls [vm, vn] (safe_mk_eq (mk_le (mk_suc vm) vn) (mk_lt vm vn))"
definition g_lt_suc_le :: hterm where
  "g_lt_suc_le = mk_foralls [vm, vn] (safe_mk_eq (mk_lt vm (mk_suc vn)) (mk_le vm vn))"
definition g_le_lt_eq :: hterm where
  "g_le_lt_eq = mk_foralls [vm, vn]
      (safe_mk_eq (mk_le vm vn) (mk_disj (mk_lt vm vn) (safe_mk_eq vm vn)))"

definition g_len_rev :: hterm where
  "g_len_rev = mk_forall (lv ''x'') (safe_mk_eq (mk_len (mk_rev (lv ''x''))) (mk_len (lv ''x'')))"
definition g_rev_rev :: hterm where
  "g_rev_rev = mk_forall (lv ''x'') (safe_mk_eq (mk_rev (mk_rev (lv ''x''))) (lv ''x''))"
definition g_len_append :: hterm where
  "g_len_append = mk_foralls [lv ''x'', lv ''y'']
      (safe_mk_eq (mk_len (mk_append (lv ''x'') (lv ''y''))) (mk_add (mk_len (lv ''x'')) (mk_len (lv ''y''))))"
definition g_append_assoc :: hterm where
  "g_append_assoc = mk_foralls [lv ''x'', lv ''y'', lv ''z'']
      (safe_mk_eq (mk_append (lv ''x'') (mk_append (lv ''y'') (lv ''z'')))
                  (mk_append (mk_append (lv ''x'') (lv ''y'')) (lv ''z'')))"
definition g_append_nil :: hterm where
  "g_append_nil = mk_forall (lv ''x'') (safe_mk_eq (mk_append (lv ''x'') nil_c) (lv ''x''))"

lemma examples_BME:
  "proves (nat_ctx bme_order) 40 g_add_zero
   \<and> proves (nat_ctx bme_order) 40 g_add_assoc
   \<and> proves (nat_ctx bme_order) 40 g_suc_add_one
   \<and> proves (nat_ctx bme_order) 40 g_add_suc
   \<and> proves (nat_ctx bme_order) 40 g_add_comm
   \<and> proves (nat_ctx bme_order) 40 g_mul_zero
   \<and> proves (nat_ctx bme_order) 40 g_mul_comm
   \<and> proves (nat_ctx bme_order) 40 g_distrib
   \<and> proves (nat_ctx bme_order) 40 g_add_cancel
   \<and> proves (nat_ctx bme_order) 40 g_le_suc_lt
   \<and> proves (nat_ctx bme_order) 40 g_lt_suc_le
   \<and> proves (nat_ctx bme_order) 40 g_le_lt_eq
   \<and> proves (list_ctx bme_order) 40 g_len_rev
   \<and> proves (list_ctx bme_order) 40 g_rev_rev
   \<and> proves (list_ctx bme_order) 40 g_len_append
   \<and> proves (list_ctx bme_order) 40 g_append_assoc
   \<and> proves (list_ctx bme_order) 40 g_append_nil"
  by eval

text \<open>The extended system with Aderhold's generalization and generalization of variables apart
  additionally proves associativity of multiplication.\<close>

lemma examples_BMF:
  "proves (nat_ctx bmf_order) 40 g_mul_assoc
   \<and> proves (nat_ctx bmf_order) 40 g_mul_comm
   \<and> proves (list_ctx bmf_order) 40 g_rev_rev"
  by eval

text \<open>The Tautology heuristic proves general propositional tautologies, e.g.
  @{text "(x \<or> y) \<or> (\<not>x \<and> \<not>y)"}, which has no complementary literal pair.\<close>

lemma taut_heuristic_example:
  "(case h_taut (nat_ctx bmf_order) False
          (mk_disj (mk_disj (Var ''x'' bool_ty) (Var ''y'' bool_ty))
                   (mk_conj (mk_neg (Var ''x'' bool_ty)) (mk_neg (Var ''y'' bool_ty)))) of
      HProved th \<Rightarrow> hyp th = [] | _ \<Rightarrow> False)"
  by eval


section \<open>Evaluation set\<close>

text \<open>A set of theorems from HOL Light's arithmetic (@{text arith.ml}/@{text num.ml}) and list theory,
  given to the prover as conjectures, as in the paper's evaluation (Section 5).  @{text eval_report}
  lists, for each theorem, whether BMF proved it and the numbers of steps, inductions and
  generalizations.\<close>

definition vq :: hterm where "vq = nm ''q''"

definition ar :: "string \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> string \<times> hterm" where
  "ar name vs t = (name, mk_foralls vs t)"

definition eqn :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" (infix "\<approx>" 50) where "eqn = safe_mk_eq"

definition eval_set :: "(string \<times> hterm) list" where
  "eval_set =
    [ ar ''ADD_0'' [vm] (mk_add vm zero_c \<approx> vm),
      ar ''ADD_SUC'' [vm, vn] (mk_add vm (mk_suc vn) \<approx> mk_suc (mk_add vm vn)),
      ar ''ADD_SYM'' [vm, vn] (mk_add vm vn \<approx> mk_add vn vm),
      ar ''ADD_ASSOC'' [vm, vn, vk] (mk_add vm (mk_add vn vk) \<approx> mk_add (mk_add vm vn) vk),
      ar ''ADD_EQ_0'' [vm, vn] (((mk_add vm vn) \<approx> zero_c) \<approx> mk_conj (vm \<approx> zero_c) (vn \<approx> zero_c)),
      ar ''EQ_ADD_LCANCEL'' [vm, vn, vk] ((mk_add vm vn \<approx> mk_add vm vk) \<approx> (vn \<approx> vk)),
      ar ''EQ_ADD_RCANCEL'' [vm, vn, vk] ((mk_add vm vk \<approx> mk_add vn vk) \<approx> (vm \<approx> vn)),
      ar ''ADD_AC_1'' [vm, vn, vk] (mk_add vm (mk_add vn vk) \<approx> mk_add vn (mk_add vm vk)),
      ar ''MULT_0'' [vm] (mk_mul vm zero_c \<approx> zero_c),
      ar ''MULT_SUC'' [vm, vn] (mk_mul vm (mk_suc vn) \<approx> mk_add vm (mk_mul vm vn)),
      ar ''MULT_SYM'' [vm, vn] (mk_mul vm vn \<approx> mk_mul vn vm),
      ar ''MULT_ASSOC'' [vm, vn, vk] (mk_mul vm (mk_mul vn vk) \<approx> mk_mul (mk_mul vm vn) vk),
      ar ''LEFT_ADD_DISTRIB'' [vm, vn, vk] (mk_mul vm (mk_add vn vk) \<approx> mk_add (mk_mul vm vn) (mk_mul vm vk)),
      ar ''RIGHT_ADD_DISTRIB'' [vm, vn, vk] (mk_mul (mk_add vm vn) vk \<approx> mk_add (mk_mul vm vk) (mk_mul vn vk)),
      ar ''MULT_1'' [vm] (mk_mul vm (mk_suc zero_c) \<approx> vm),
      ar ''EXP_1'' [vm] (mk_exp vm (mk_suc zero_c) \<approx> vm),
      ar ''ONE_EXP'' [vn] (mk_exp (mk_suc zero_c) vn \<approx> mk_suc zero_c),
      ar ''EXP_ADD'' [vm, vn, vk] (mk_exp vm (mk_add vn vk) \<approx> mk_mul (mk_exp vm vn) (mk_exp vm vk)),
      ar ''MULT_EXP'' [vm, vn, vk] (mk_exp (mk_mul vm vn) vk \<approx> mk_mul (mk_exp vm vk) (mk_exp vn vk)),
      ar ''EXP_MULT'' [vm, vn, vk] (mk_exp vm (mk_mul vn vk) \<approx> mk_exp (mk_exp vm vn) vk),
      ar ''LE_REFL'' [vm] (mk_le vm vm),
      ar ''LE_0'' [vn] (mk_le zero_c vn),
      ar ''LT_REFL'' [vm] (mk_not (mk_lt vm vm)),
      ar ''LT_0'' [vn] (mk_lt zero_c (mk_suc vn)),
      ar ''LE_SUC_LT'' [vm, vn] (mk_le (mk_suc vm) vn \<approx> mk_lt vm vn),
      ar ''LT_SUC_LE'' [vm, vn] (mk_lt vm (mk_suc vn) \<approx> mk_le vm vn),
      ar ''LE_LT'' [vm, vn] (mk_le vm vn \<approx> mk_disj (mk_lt vm vn) (vm \<approx> vn)),
      ar ''LE_TRANS'' [vm, vn, vk] (mk_imp (mk_le vm vn) (mk_imp (mk_le vn vk) (mk_le vm vk))),
      ar ''LE_ANTISYM'' [vm, vn] (mk_conj (mk_le vm vn) (mk_le vn vm) \<approx> (vm \<approx> vn)),
      ar ''LE_ADD'' [vm, vn] (mk_le vm (mk_add vm vn)),
      ar ''LT_IMP_LE'' [vm, vn] (mk_imp (mk_lt vm vn) (mk_le vm vn)),
      ar ''NOT_LE'' [vm, vn] (mk_not (mk_le vm vn) \<approx> mk_lt vn vm),
      ar ''NOT_LT'' [vm, vn] (mk_not (mk_lt vm vn) \<approx> mk_le vn vm),
      ar ''LE_ADD_LCANCEL'' [vm, vn, vk] (mk_le (mk_add vm vn) (mk_add vm vk) \<approx> mk_le vn vk),
      ar ''LT_ADD_LCANCEL'' [vm, vn, vk] (mk_lt (mk_add vm vn) (mk_add vm vk) \<approx> mk_lt vn vk),
      ar ''LE_MULT_LCANCEL_0'' [vm] (mk_le zero_c (mk_mul vm vm)),
      ar ''LT_TRANS'' [vm, vn, vk] (mk_imp (mk_lt vm vn) (mk_imp (mk_lt vn vk) (mk_lt vm vk))),
      ar ''LT_TRICHOTOMY'' [vm, vn] (mk_disj (mk_lt vm vn) (mk_disj (vm \<approx> vn) (mk_lt vn vm))),
      ar ''SUB_0'' [vm] (mk_sub zero_c vm \<approx> zero_c),
      ar ''SUB_REFL'' [vm] (mk_sub vm vm \<approx> zero_c),
      ar ''ADD_SUB'' [vm, vn] (mk_sub (mk_add vm vn) vn \<approx> vm),
      ar ''EVEN_ADD'' [vm, vn] (mk_even (mk_add vm vn) \<approx> (mk_even vm \<approx> mk_even vn)),
      ar ''EVEN_MULT'' [vm, vn] (mk_even (mk_mul vm vn) \<approx> mk_disj (mk_even vm) (mk_even vn)),
      ar ''EVEN_DOUBLE'' [vm] (mk_even (mk_add vm vm)),
      ar ''APPEND_NIL'' [lv ''x''] (mk_append (lv ''x'') nil_c \<approx> lv ''x''),
      ar ''APPEND_ASSOC'' [lv ''x'', lv ''y'', lv ''z'']
         (mk_append (lv ''x'') (mk_append (lv ''y'') (lv ''z'')) \<approx> mk_append (mk_append (lv ''x'') (lv ''y'')) (lv ''z'')),
      ar ''LENGTH_APPEND'' [lv ''x'', lv ''y'']
         (mk_len (mk_append (lv ''x'') (lv ''y'')) \<approx> mk_add (mk_len (lv ''x'')) (mk_len (lv ''y''))),
      ar ''LENGTH_REVERSE'' [lv ''x''] (mk_len (mk_rev (lv ''x'')) \<approx> mk_len (lv ''x'')),
      ar ''REVERSE_REVERSE'' [lv ''x''] (mk_rev (mk_rev (lv ''x'')) \<approx> lv ''x''),
      ar ''REVERSE_APPEND'' [lv ''x'', lv ''y'']
         (mk_rev (mk_append (lv ''x'') (lv ''y'')) \<approx> mk_append (mk_rev (lv ''y'')) (mk_rev (lv ''x''))) ]"

definition eval_one :: "string \<times> hterm \<Rightarrow> string" where
  "eval_one p =
     (let cx = (if tm_size (snd p) > 0 then list_ctx bmf_order else nat_ctx bmf_order)
      in case bm_prove cx 40 (snd p) of
           (r, st) \<Rightarrow> fst p @ '' '' @ (case r of Some th \<Rightarrow> if hyp th = [] \<and> aconv (concl th) (snd p) then ''OK'' else ''BAD'' | None \<Rightarrow> ''FAIL'')
                     @ '' '' @ nat_str (w_steps st) @ '' '' @ nat_str (w_inds st) @ '' '' @ nat_str (w_gens st))"

definition eval_report :: "string list" where
  "eval_report = map eval_one eval_set"

definition eval_ok :: "string \<times> hterm \<Rightarrow> bool" where
  "eval_ok p = (case bm_prove (list_ctx bmf_order) 40 (snd p) of
                  (Some th, _) \<Rightarrow> hyp th = [] \<and> aconv (concl th) (snd p)
                | (None, _) \<Rightarrow> False)"

definition eval_proved :: "string list" where
  "eval_proved = [''ADD_0'', ''ADD_SUC'', ''ADD_SYM'', ''ADD_ASSOC'', ''ADD_EQ_0'', ''EQ_ADD_LCANCEL'', ''ADD_AC_1'', ''MULT_0'', ''MULT_SUC'', ''MULT_SYM'', ''MULT_ASSOC'', ''LEFT_ADD_DISTRIB'', ''RIGHT_ADD_DISTRIB'', ''MULT_1'', ''EXP_1'', ''ONE_EXP'', ''LE_REFL'', ''LE_0'', ''LT_0'', ''LE_SUC_LT'', ''LT_SUC_LE'', ''LE_LT'', ''LE_TRANS'', ''LT_IMP_LE'', ''LT_TRANS'', ''SUB_0'', ''APPEND_NIL'', ''APPEND_ASSOC'', ''LENGTH_APPEND'', ''LENGTH_REVERSE'', ''REVERSE_REVERSE'', ''REVERSE_APPEND'']"

text \<open>BMF proves 32 of the 50 conjectures (64%; the paper reports 47% for its first test set).
  The others need lemmas that the waterfall cannot speculate (e.g. @{text "SUC m \<noteq> m"} for
  @{text "\<not> m < m"}, commutativity under a cancellation law, or induction on a term rather than a
  variable for @{text "m \<le> m + n"}); @{text eval_report} lists them with their step counts.\<close>

lemma eval_set_proved: "length eval_set = 50 \<and> list_all eval_ok (filter (\<lambda>p. fst p \<in> set eval_proved) eval_set)
    \<and> length (filter (\<lambda>p. fst p \<in> set eval_proved) eval_set) = 32"
  by eval

end
