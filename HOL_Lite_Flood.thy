theory HOL_Lite_Flood
  imports HOL_Lite_Waterfall HOL_Lite_Saturation
begin

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
  The finite forward operators of HOL_Lite_Saturation (@{text step_refl}, @{text step_trans}, ...)
  live inside the @{locale hol_lite_axs} context, so they take the fixed signature and axiom
  oracle implicitly; that keeps their statements short but means they cannot be handed to the
  code generator without an interpretation. The definitions below give a single, explicit-argument
  implementation of each rule step, executable by @{command value} or the @{text eval} proof
  method; only the soundness connection to the semantic \<open>step_*\<close> operators lives inside the
  locale. These definitions are the sole implementation of each rule step: @{text runtime_step}
  below composes them directly rather than restating the rule bodies a second time.\<close>

text \<open>Region membership is decided by a direct predicate instead of a linear search in the
  enumerated list @{const enum_tm}; the two agree by @{text tm_ok_iff}.  Every candidate
  sequent produced by a rule step is checked, so this test dominates the cost of a round.\<close>

definition ty_ok :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> bool" where
  "ty_ok ns \<Sigma> r \<tau> = (wf_ty \<Sigma> \<tau> \<and> ty_size \<tau> \<le> r \<and> ty_names \<tau> \<subseteq> set ns)"

lemma ty_ok_iff [simp]: "ty_ok ns \<Sigma> r \<tau> \<longleftrightarrow> \<tau> \<in> Ty (set ns) \<Sigma> r"
  by (simp add: ty_ok_def Ty_def)

fun wf_tm_ex :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool" where
  "wf_tm_ex ns \<Sigma> r (Fv x \<tau>) = (x \<in> set ns \<and> ty_ok ns \<Sigma> r \<tau>)"
| "wf_tm_ex ns \<Sigma> r (Bv i) = (i \<le> r)"
| "wf_tm_ex ns \<Sigma> r (Cst c \<tau>) = (c \<in> set ns \<and> ty_ok ns \<Sigma> r \<tau>)"
| "wf_tm_ex ns \<Sigma> r (App f a) = (wf_tm_ex ns \<Sigma> r f \<and> wf_tm_ex ns \<Sigma> r a)"
| "wf_tm_ex ns \<Sigma> r (Abs \<tau> b) = (ty_ok ns \<Sigma> r \<tau> \<and> wf_tm_ex ns \<Sigma> r b)"

lemma wf_tm_ex_iff [simp]: "wf_tm_ex ns \<Sigma> r t \<longleftrightarrow> wf_tm (set ns) \<Sigma> r t"
  by (induction t) simp_all

definition tm_ok :: "name list \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool" where
  "tm_ok ns \<Sigma> r t = (tm_size t \<le> r \<and> wf_tm_ex ns \<Sigma> r t \<and> typeof \<Sigma> [] t \<noteq> None)"

lemma tm_ok_iff: "tm_ok ns \<Sigma> r t \<longleftrightarrow> t \<in> set (enum_tm ns \<Sigma> r)"
  by (simp add: tm_ok_def set_enum_tm Tm_wt_def Tm_def)

definition runtime_bounded :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> bool" where
  "runtime_bounded \<Sigma> ns r p = ((\<forall>t\<in>fst p. tm_ok ns \<Sigma> r t) \<and> tm_ok ns \<Sigma> r (snd p))"

lemma runtime_bounded_iff [simp]:
  "runtime_bounded \<Sigma> ns r p \<longleftrightarrow> p \<in> Sequent_r (set ns) \<Sigma> r"
  by (cases p) (auto simp: runtime_bounded_def Sequent_r_def tm_ok_iff set_enum_tm subset_iff)

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
  global, explicit-argument executable step used by the Flood driver below.
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

section \<open>Executable flood\<close>

text \<open>
  Flood is the forward counterpart of the waterfall.  The waterfall starts from the goal and
  rewrites it into subgoals.  Flood ignores the goal's shape: for a name list @{text ns} and a
  size radius @{text r} it saturates the finite sequent region under all rules until no new
  sequent is generated, and only then asks whether the goal is in the result.

  @{text flood_decide} decides exactly the clipped derivations @{text "bderiv (set ns) r"} of
  that region.  @{text flood_processor} turns it into a waterfall processor that returns
  @{text Closed} or @{text Unchanged}, never @{text Subgoals}.  A terminating axiom enumerator
  satisfying the locale axiom specification must be supplied.

  @{text ns} is the finite name set @{text "N = set ns"}; free variables, constants, type
  variables and type constructors all draw from it.  It must contain every name of the goal, of
  each axiom to be used, and of every intermediate sequent of the intended proof
  (@{text derivable_iff_bderiv} only asserts that some finite @{text N} and @{text r} exist; it
  does not compute them).  Enlarging @{text ns} or @{text r} never loses a derivation but grows
  the search exponentially: a region with m well-typed terms contains 2^m * m sequents.

  A positive answer is a proof.  A negative answer only refutes derivability inside this region,
  so Flood is not a decision procedure for unbounded derivability.  Retrying with larger
  @{text ns} and @{text r} is the caller's job; a processor list holds finitely many attempts.
\<close>

fun flood_rounds :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "flood_rounds \<Sigma> axs ns r 0 S = S"
| "flood_rounds \<Sigma> axs ns r (Suc k) S =
    (let T = remdups (S @ runtime_step \<Sigma> axs ns r S)
     in if set T = set S then S else flood_rounds \<Sigma> axs ns r k T)"

definition flood_bound :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> nat" where
  "flood_bound \<Sigma> ns r = 2 ^ length (enum_tm ns \<Sigma> r) * length (enum_tm ns \<Sigma> r)"

definition flood_decide :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
    (tm set \<times> tm) \<Rightarrow> bool" where
  "flood_decide \<Sigma> axs ns r p =
    (p \<in> set (flood_rounds \<Sigma> axs ns r (flood_bound \<Sigma> ns r) []))"

definition flood_processor :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> processor" where
  "flood_processor \<Sigma> axs ns r g =
    (if flood_decide \<Sigma> axs ns r (set (fst g), snd g) then Closed else Unchanged)"

context hol_lite_axs
begin

lemma set_flood_rounds:
  assumes sub: "set S \<subseteq> Sequent_r (set ns) \<Sigma> r"
  shows "set (flood_rounds \<Sigma> axs ns r k S) = (grow_r (set ns) r ^^ k) (set S)"
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
    have "set (flood_rounds \<Sigma> axs ns r (Suc k) S) = (grow_r (set ns) r ^^ k) (set ?T)"
      using False Suc.IH[OF Tsub] by (simp add: Let_def)
    also have "... = (grow_r (set ns) r ^^ Suc k) (set S)"
      by (simp only: Tset funpow_Suc_right o_apply)
    finally show ?thesis .
  qed
qed

lemma flood_bound_card:
  "flood_bound \<Sigma> ns r = card (Sequent_r (set ns) \<Sigma> r)"
proof -
  have distinct: "distinct (enum_tm ns \<Sigma> r)" by (simp add: enum_tm_def)
  show ?thesis
    by (simp add: flood_bound_def Sequent_r_def set_enum_tm[symmetric] distinct card_Pow distinct_card)
qed

theorem flood_decide_iff_bderiv:
  "flood_decide \<Sigma> axs ns r p \<longleftrightarrow> bderiv (set ns) r p"
  using set_flood_rounds[of "[]" ns r "flood_bound \<Sigma> ns r"]
    bounded_iteration_iff_bderiv[of "set ns" p r]
  by (simp add: flood_decide_def flood_bound_card iterate_r_def)

corollary flood_decide_sound:
  "flood_decide \<Sigma> axs ns r (\<Gamma>,c) \<Longrightarrow> derivable \<Gamma> c"
  using flood_decide_iff_bderiv bderiv_sound by blast

lemma sound_flood_processor: "sound_proc (flood_processor \<Sigma> axs ns r)"
  unfolding sound_proc_def flood_processor_def
  using flood_decide_sound by (auto simp: provable_iff)

lemma waterfall_flood_complete:
  "waterfall 1 [flood_processor \<Sigma> axs ns r] (H,c) = [] \<longleftrightarrow>
   bderiv (set ns) r (set H,c)"
  by (simp add: flood_processor_def flood_decide_iff_bderiv)

end

end
