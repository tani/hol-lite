theory HOL_Lite_Executable_Enum
  imports HOL_Lite_L8
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

end
