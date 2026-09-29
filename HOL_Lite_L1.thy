theory HOL_Lite_L1
  imports HOL_Lite_Check
begin

section \<open>Bounded exhaustive search spaces\<close>

text \<open>
  This theory sets up, for a fixed finite name set @{term N} and size bound @{term r}, the
  finite search spaces @{term "Ty N \<Sigma> r"} (well-formed types), @{term "Tm N \<Sigma> r"} (syntactically
  well-formed terms, not necessarily typeable) and @{term "Tm_wt N \<Sigma> r"} (the typeable subset)
  that bounded exhaustive search enumerates.
\<close>

subsection \<open>Size and name measures\<close>

fun ty_size :: "ty \<Rightarrow> nat" where
  "ty_size (TyVar a) = 1"
| "ty_size (TyApp c ts) = 1 + sum_list (map ty_size ts)"

fun ty_names :: "ty \<Rightarrow> name set" where
  "ty_names (TyVar a) = {a}"
| "ty_names (TyApp c ts) = insert c (\<Union>(set (map ty_names ts)))"

fun tm_size :: "tm \<Rightarrow> nat" where
  "tm_size (Fv x \<tau>) = 1 + ty_size \<tau>"
| "tm_size (Bv i) = 1"
| "tm_size (Cst c \<tau>) = 1 + ty_size \<tau>"
| "tm_size (App f a) = 1 + tm_size f + tm_size a"
| "tm_size (Abs \<tau> b) = 1 + ty_size \<tau> + tm_size b"

fun tm_names :: "tm \<Rightarrow> name set" where
  "tm_names (Fv x \<tau>) = insert x (ty_names \<tau>)"
| "tm_names (Bv i) = {}"
| "tm_names (Cst c \<tau>) = insert c (ty_names \<tau>)"
| "tm_names (App f a) = tm_names f \<union> tm_names a"
| "tm_names (Abs \<tau> b) = ty_names \<tau> \<union> tm_names b"

text \<open>Largest de Bruijn index occurring anywhere in a term (0 if none).\<close>

fun tm_maxbv :: "tm \<Rightarrow> nat" where
  "tm_maxbv (Fv x \<tau>) = 0"
| "tm_maxbv (Bv i) = i"
| "tm_maxbv (Cst c \<tau>) = 0"
| "tm_maxbv (App f a) = max (tm_maxbv f) (tm_maxbv a)"
| "tm_maxbv (Abs \<tau> b) = tm_maxbv b"

text \<open>All type annotations occurring in a term are well-formed (no typing of the term itself).\<close>

fun wf_tm_ty :: "hsig \<Rightarrow> tm \<Rightarrow> bool" where
  "wf_tm_ty \<Sigma> (Fv x \<tau>) = wf_ty \<Sigma> \<tau>"
| "wf_tm_ty \<Sigma> (Bv i) = True"
| "wf_tm_ty \<Sigma> (Cst c \<tau>) = wf_ty \<Sigma> \<tau>"
| "wf_tm_ty \<Sigma> (App f a) = (wf_tm_ty \<Sigma> f \<and> wf_tm_ty \<Sigma> a)"
| "wf_tm_ty \<Sigma> (Abs \<tau> b) = (wf_ty \<Sigma> \<tau> \<and> wf_tm_ty \<Sigma> b)"

lemma ty_size_pos [simp]: "1 \<le> ty_size \<tau>"
  by (cases \<tau>) simp_all

lemma tm_size_pos [simp]: "1 \<le> tm_size t"
  by (cases t) simp_all

subsection \<open>A finiteness helper for lists of bounded length\<close>

lemma finite_lists_length_le:
  assumes "finite A"
  shows "finite {xs. set xs \<subseteq> A \<and> length xs \<le> n}"
proof (induction n)
  case 0
  have "{xs. set xs \<subseteq> A \<and> length xs \<le> 0} = {[]}" by auto
  then show ?case by simp
next
  case (Suc n)
  have eq: "{xs. set xs \<subseteq> A \<and> length xs \<le> Suc n}
      = {xs. set xs \<subseteq> A \<and> length xs \<le> n} \<union> (\<Union>a\<in>A. (#) a ` {xs. set xs \<subseteq> A \<and> length xs \<le> n})"
    (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix xs assume "xs \<in> ?L"
    then show "xs \<in> ?R"
    proof (cases "length xs \<le> n")
      case True
      with \<open>xs \<in> ?L\<close> show ?thesis by auto
    next
      case False
      with \<open>xs \<in> ?L\<close> obtain a ys where "xs = a # ys" and "length ys \<le> n"
        by (cases xs) auto
      with \<open>xs \<in> ?L\<close> show ?thesis by auto
    qed
  next
    fix xs assume "xs \<in> ?R"
    then show "xs \<in> ?L" by auto
  qed
  from assms Suc.IH show ?case by (simp add: eq)
qed

subsection \<open>The type search space\<close>

definition Ty :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> ty set" where
  "Ty N \<Sigma> r = {\<tau>. wf_ty \<Sigma> \<tau> \<and> ty_size \<tau> \<le> r \<and> ty_names \<tau> \<subseteq> N}"

lemma Ty_memI [intro]:
  "wf_ty \<Sigma> \<tau> \<Longrightarrow> ty_size \<tau> \<le> r \<Longrightarrow> ty_names \<tau> \<subseteq> N \<Longrightarrow> \<tau> \<in> Ty N \<Sigma> r"
  by (simp add: Ty_def)

lemma Ty_memD:
  "\<tau> \<in> Ty N \<Sigma> r \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> ty_size \<tau> \<le> r \<and> ty_names \<tau> \<subseteq> N"
  by (simp add: Ty_def)

lemma Ty_mono_r: "r \<le> r' \<Longrightarrow> Ty N \<Sigma> r \<subseteq> Ty N \<Sigma> r'"
  unfolding Ty_def by auto

lemma Ty_mono_N: "N \<subseteq> N' \<Longrightarrow> Ty N \<Sigma> r \<subseteq> Ty N' \<Sigma> r"
  unfolding Ty_def by auto

subsection \<open>Finiteness of the type search space\<close>

text \<open>
  An explicit finite superset of @{term "Ty N \<Sigma> r"}, built by recursion on @{term r} alone
  (independently of @{term \<Sigma>}), used only to prove finiteness.
\<close>

fun ty_univ :: "name set \<Rightarrow> nat \<Rightarrow> ty set" where
  "ty_univ N 0 = {}"
| "ty_univ N (Suc r) =
     TyVar ` N \<union> (\<Union>c\<in>N. TyApp c ` {ts. length ts \<le> r \<and> set ts \<subseteq> ty_univ N r})"

lemma finite_ty_univ: "finite N \<Longrightarrow> finite (ty_univ N r)"
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  then have "finite {ts. length ts \<le> r \<and> set ts \<subseteq> ty_univ N r}"
  proof -
    have "{ts. length ts \<le> r \<and> set ts \<subseteq> ty_univ N r}
        = {xs. set xs \<subseteq> ty_univ N r \<and> length xs \<le> r}"
      by auto
    then show ?thesis using finite_lists_length_le[of "ty_univ N r" r] Suc.IH Suc.prems
      by simp
  qed
  with Suc.IH Suc.prems show ?case by simp
qed

lemma Ty_subset_ty_univ: "wf_ty \<Sigma> \<tau> \<Longrightarrow> ty_size \<tau> \<le> r \<Longrightarrow> ty_names \<tau> \<subseteq> N \<Longrightarrow> \<tau> \<in> ty_univ N r"
proof (induction \<tau> arbitrary: r rule: ty.induct)
  case (TyVar a)
  then obtain r' where r: "r = Suc r'" by (cases r) auto
  from TyVar show ?case by (simp add: r)
next
  case (TyApp c ts)
  from TyApp.prems obtain r' where r: "r = Suc r'"
    by (cases r) auto
  from TyApp.prems have wf: "tyar \<Sigma> c = Some (length ts)" "\<forall>t\<in>set ts. wf_ty \<Sigma> t"
    by simp_all
  from TyApp.prems r have sz: "1 + sum_list (map ty_size ts) \<le> Suc r'" by simp
  then have sz': "sum_list (map ty_size ts) \<le> r'" by simp
  have len: "length ts \<le> r'"
  proof -
    have "length ts \<le> sum_list (map ty_size ts)"
    proof (induction ts)
      case Nil
      then show ?case by simp
    next
      case (Cons a ts)
      have "length (a # ts) = Suc (length ts)" by simp
      moreover have "sum_list (map ty_size (a # ts)) = ty_size a + sum_list (map ty_size ts)"
        by simp
      ultimately show ?case using Cons.IH ty_size_pos[of a] by linarith
    qed
    with sz' show ?thesis by simp
  qed
  from TyApp.prems have nm: "c \<in> N" "\<forall>t\<in>set ts. ty_names t \<subseteq> N"
    by auto
  have "\<forall>t\<in>set ts. ty_size t \<le> r'"
  proof
    fix t assume t: "t \<in> set ts"
    then have "ty_size t \<le> sum_list (map ty_size ts)"
      by (induction ts) auto
    with sz' show "ty_size t \<le> r'" by simp
  qed
  with wf nm TyApp.IH have ts_mem: "\<forall>t\<in>set ts. t \<in> ty_univ N r'"
    by auto
  have "TyApp c ts \<in> TyApp c ` {ts. length ts \<le> r' \<and> set ts \<subseteq> ty_univ N r'}"
    using len ts_mem by auto
  with nm(1) have "TyApp c ts \<in> ty_univ N (Suc r')"
    by auto
  with r show ?case by simp
qed

lemma finite_Ty: "finite N \<Longrightarrow> finite (Ty N \<Sigma> r)"
  using Ty_subset_ty_univ[of \<Sigma> _ r N] finite_ty_univ[of N r]
  by (intro finite_subset[of "Ty N \<Sigma> r" "ty_univ N r"]) (auto simp: Ty_def)

subsection \<open>Exhaustiveness of the type search space\<close>

lemma Ty_exhaust: "wf_ty \<Sigma> \<tau> \<Longrightarrow> ty_names \<tau> \<subseteq> N \<Longrightarrow> \<tau> \<in> Ty N \<Sigma> (ty_size \<tau>)"
  by (simp add: Ty_def)

lemma Ty_exhaust_ex: "wf_ty \<Sigma> \<tau> \<Longrightarrow> ty_names \<tau> \<subseteq> N \<Longrightarrow> \<exists>r. \<tau> \<in> Ty N \<Sigma> r"
  using Ty_exhaust by blast

subsection \<open>The term search space\<close>

text \<open>
  A term is a member of @{term "wf_tm N \<Sigma> r"} iff every free-variable/constant name it uses is
  in @{term N}, every type annotation it carries lies in @{term "Ty N \<Sigma> r"}, and every loose
  bound index is at most @{term r}. This is a purely syntactic notion; it does not require the
  term to be typeable.
\<close>

fun wf_tm :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> bool" where
  "wf_tm N \<Sigma> r (Fv x \<tau>) = (x \<in> N \<and> \<tau> \<in> Ty N \<Sigma> r)"
| "wf_tm N \<Sigma> r (Bv i) = (i \<le> r)"
| "wf_tm N \<Sigma> r (Cst c \<tau>) = (c \<in> N \<and> \<tau> \<in> Ty N \<Sigma> r)"
| "wf_tm N \<Sigma> r (App f a) = (wf_tm N \<Sigma> r f \<and> wf_tm N \<Sigma> r a)"
| "wf_tm N \<Sigma> r (Abs \<tau> b) = (\<tau> \<in> Ty N \<Sigma> r \<and> wf_tm N \<Sigma> r b)"

definition Tm :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm set" where
  "Tm N \<Sigma> r = {t. tm_size t \<le> r \<and> wf_tm N \<Sigma> r t}"

text \<open>
  The typeable subset of @{term "Tm N \<Sigma> r"}: terms admitting a type in the empty (loose-index)
  context, as decided by the executable checker @{const typeof} from \<open>HOL_Lite_Check\<close>.
\<close>

definition Tm_wt :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> tm set" where
  "Tm_wt N \<Sigma> r = {t \<in> Tm N \<Sigma> r. typeof \<Sigma> [] t \<noteq> None}"

lemma Tm_memI [intro]:
  "tm_size t \<le> r \<Longrightarrow> wf_tm N \<Sigma> r t \<Longrightarrow> t \<in> Tm N \<Sigma> r"
  by (simp add: Tm_def)

lemma Tm_memD:
  "t \<in> Tm N \<Sigma> r \<Longrightarrow> tm_size t \<le> r \<and> wf_tm N \<Sigma> r t"
  by (simp add: Tm_def)

subsection \<open>Monotonicity of the term search space\<close>

lemma wf_tm_mono_r: "r \<le> r' \<Longrightarrow> wf_tm N \<Sigma> r t \<Longrightarrow> wf_tm N \<Sigma> r' t"
proof (induction t arbitrary: rule: tm.induct)
  case (Fv x \<tau>)
  then show ?case using Ty_mono_r[of r r' N \<Sigma>] by auto
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  then show ?case using Ty_mono_r[of r r' N \<Sigma>] by auto
next
  case (App f a)
  then show ?case by simp
next
  case (Abs \<tau> b)
  then show ?case using Ty_mono_r[of r r' N \<Sigma>] by auto
qed

lemma wf_tm_mono_N: "N \<subseteq> N' \<Longrightarrow> wf_tm N \<Sigma> r t \<Longrightarrow> wf_tm N' \<Sigma> r t"
proof (induction t arbitrary: rule: tm.induct)
  case (Fv x \<tau>)
  then show ?case using Ty_mono_N[of N N' \<Sigma> r] by auto
next
  case (Bv i)
  then show ?case by simp
next
  case (Cst c \<tau>)
  then show ?case using Ty_mono_N[of N N' \<Sigma> r] by auto
next
  case (App f a)
  then show ?case by simp
next
  case (Abs \<tau> b)
  then show ?case using Ty_mono_N[of N N' \<Sigma> r] by auto
qed

lemma Tm_mono_r: "r \<le> r' \<Longrightarrow> Tm N \<Sigma> r \<subseteq> Tm N \<Sigma> r'"
  unfolding Tm_def using wf_tm_mono_r order_trans by fastforce

lemma Tm_mono_N: "N \<subseteq> N' \<Longrightarrow> Tm N \<Sigma> r \<subseteq> Tm N' \<Sigma> r"
  unfolding Tm_def using wf_tm_mono_N by fastforce

lemma Tm_wt_mono_r: "r \<le> r' \<Longrightarrow> Tm_wt N \<Sigma> r \<subseteq> Tm_wt N \<Sigma> r'"
  unfolding Tm_wt_def using Tm_mono_r[of r r' N \<Sigma>] by auto

lemma Tm_wt_mono_N: "N \<subseteq> N' \<Longrightarrow> Tm_wt N \<Sigma> r \<subseteq> Tm_wt N' \<Sigma> r"
  unfolding Tm_wt_def using Tm_mono_N[of N N' \<Sigma> r] by auto

subsection \<open>Finiteness of the term search space\<close>

text \<open>
  An explicit finite superset of @{term "Tm N \<Sigma> r"}, used only to prove finiteness.
\<close>

fun tm_univ2 :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tm set" where
  "tm_univ2 N \<Sigma> r 0 = {}"
| "tm_univ2 N \<Sigma> r (Suc k) =
     (\<Union>x\<in>N. Fv x ` Ty N \<Sigma> r) \<union>
     Bv ` {0..r} \<union>
     (\<Union>c\<in>N. Cst c ` Ty N \<Sigma> r) \<union>
     (\<lambda>(f, a). App f a) ` (tm_univ2 N \<Sigma> r k \<times> tm_univ2 N \<Sigma> r k) \<union>
     (\<lambda>(\<tau>, b). Abs \<tau> b) ` (Ty N \<Sigma> r \<times> tm_univ2 N \<Sigma> r k)"

text \<open>
  @{const wf_tm} threads the same bound @{term r} unchanged through the whole term (it governs
  every loose index and every type annotation, at any depth), so only the size argument
  @{term k} of @{const tm_univ2} decreases under recursion; @{term r} stays fixed.
\<close>

lemma finite_tm_univ2: "finite N \<Longrightarrow> finite (tm_univ2 N \<Sigma> r k)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have tyfin: "finite (Ty N \<Sigma> r)" using finite_Ty Suc.prems by simp
  have bvfin: "finite (Bv ` {0..r})" by simp
  have tmfin: "finite (tm_univ2 N \<Sigma> r k)" using Suc.IH Suc.prems by simp
  from Suc.prems tyfin bvfin tmfin show ?case
    by (auto intro!: finite_UnI finite_UN finite_imageI finite_cartesian_product)
qed

lemma Tm_subset_tm_univ2:
  "tm_size t \<le> k \<Longrightarrow> wf_tm N \<Sigma> r t \<Longrightarrow> t \<in> tm_univ2 N \<Sigma> r k"
proof (induction t arbitrary: k rule: tm.induct)
  case (Fv x \<tau>)
  then obtain k' where k: "k = Suc k'" by (cases k) auto
  from Fv show ?case by (auto simp: k)
next
  case (Bv i)
  then obtain k' where k: "k = Suc k'" by (cases k) auto
  from Bv show ?case by (simp add: k)
next
  case (Cst c \<tau>)
  then obtain k' where k: "k = Suc k'" by (cases k) auto
  from Cst show ?case by (auto simp: k)
next
  case (App f a)
  from App.prems obtain k' where k: "k = Suc k'"
    by (cases k) auto
  from App.prems have wf: "wf_tm N \<Sigma> r f" "wf_tm N \<Sigma> r a" by simp_all
  from App.prems k have sz: "tm_size f + tm_size a \<le> k'" by simp
  then have szf: "tm_size f \<le> k'" and sza: "tm_size a \<le> k'" by simp_all
  from App.IH(1)[OF szf wf(1)] have f': "f \<in> tm_univ2 N \<Sigma> r k'" .
  from App.IH(2)[OF sza wf(2)] have a': "a \<in> tm_univ2 N \<Sigma> r k'" .
  from f' a' have "App f a \<in> tm_univ2 N \<Sigma> r (Suc k')" by auto
  with k show ?case by simp
next
  case (Abs \<tau> b)
  from Abs.prems obtain k' where k: "k = Suc k'"
    by (cases k) auto
  from Abs.prems have wf: "\<tau> \<in> Ty N \<Sigma> r" "wf_tm N \<Sigma> r b" by simp_all
  from Abs.prems k have szb: "tm_size b \<le> k'" by simp
  from Abs.IH[OF szb wf(2)] have b': "b \<in> tm_univ2 N \<Sigma> r k'" .
  from wf(1) b' have "Abs \<tau> b \<in> tm_univ2 N \<Sigma> r (Suc k')" by auto
  with k show ?case by simp
qed

lemma finite_Tm: "finite N \<Longrightarrow> finite (Tm N \<Sigma> r)"
  using Tm_subset_tm_univ2[of _ r N \<Sigma> r] finite_tm_univ2[of N \<Sigma> r r]
  by (intro finite_subset[of "Tm N \<Sigma> r" "tm_univ2 N \<Sigma> r r"]) (auto simp: Tm_def)

lemma finite_Tm_wt: "finite N \<Longrightarrow> finite (Tm_wt N \<Sigma> r)"
  unfolding Tm_wt_def using finite_Tm by simp

subsection \<open>Exhaustiveness of the term search space\<close>

text \<open>
  Any syntactically well-formed term (all type annotations well-formed, all names in @{term N})
  lies in @{term "Tm N \<Sigma> r"} for @{term "r = max (tm_size t) (tm_maxbv t)"}: the size bound
  covers @{const tm_size} and every type annotation (whose size is bounded by @{const tm_size}),
  while the max with @{const tm_maxbv} additionally covers loose indices, whose value is not
  bounded by @{const tm_size} at all (@{term "tm_size (Bv i) = 1"} regardless of @{term i}).
\<close>

lemma Tm_exhaust:
  "wf_tm_ty \<Sigma> t \<Longrightarrow> tm_names t \<subseteq> N \<Longrightarrow> t \<in> Tm N \<Sigma> (max (tm_size t) (tm_maxbv t))"
proof (induction t rule: tm.induct)
  case (Fv x \<tau>)
  then show ?case unfolding Tm_def Ty_def by auto
next
  case (Bv i)
  then show ?case unfolding Tm_def by auto
next
  case (Cst c \<tau>)
  then show ?case unfolding Tm_def Ty_def by auto
next
  case (App f a)
  from App.prems have wfty: "wf_tm_ty \<Sigma> f" "wf_tm_ty \<Sigma> a" by simp_all
  from App.prems have nm: "tm_names f \<subseteq> N" "tm_names a \<subseteq> N" by auto
  from App.IH(1)[OF wfty(1) nm(1)] have f_mem: "f \<in> Tm N \<Sigma> (max (tm_size f) (tm_maxbv f))" .
  from App.IH(2)[OF wfty(2) nm(2)] have a_mem: "a \<in> Tm N \<Sigma> (max (tm_size a) (tm_maxbv a))" .
  define r where "r = max (tm_size (App f a)) (tm_maxbv (App f a))"
  have rf: "max (tm_size f) (tm_maxbv f) \<le> r" unfolding r_def by auto
  have ra: "max (tm_size a) (tm_maxbv a) \<le> r" unfolding r_def by auto
  from Tm_mono_r[OF rf] f_mem have f_mem': "f \<in> Tm N \<Sigma> r" by blast
  from Tm_mono_r[OF ra] a_mem have a_mem': "a \<in> Tm N \<Sigma> r" by blast
  from f_mem' a_mem' have wf: "wf_tm N \<Sigma> r f" "wf_tm N \<Sigma> r a" using Tm_memD by blast+
  then have wfapp: "wf_tm N \<Sigma> r (App f a)" by simp
  have szapp: "tm_size (App f a) \<le> r" unfolding r_def by auto
  from Tm_memI[OF szapp wfapp] have "App f a \<in> Tm N \<Sigma> r" .
  then show ?case unfolding r_def .
next
  case (Abs \<tau> b)
  from Abs.prems have wfty: "wf_ty \<Sigma> \<tau>" "wf_tm_ty \<Sigma> b" by simp_all
  from Abs.prems have nm: "ty_names \<tau> \<subseteq> N" "tm_names b \<subseteq> N" by auto
  from Abs.IH[OF wfty(2) nm(2)] have b_mem: "b \<in> Tm N \<Sigma> (max (tm_size b) (tm_maxbv b))" .
  define r where "r = max (tm_size (Abs \<tau> b)) (tm_maxbv (Abs \<tau> b))"
  have rb: "max (tm_size b) (tm_maxbv b) \<le> r" unfolding r_def by auto
  from Tm_mono_r[OF rb] b_mem have b_mem': "b \<in> Tm N \<Sigma> r" by blast
  from b_mem' have wfb: "wf_tm N \<Sigma> r b" using Tm_memD by blast
  have tau_ty: "\<tau> \<in> Ty N \<Sigma> r"
    unfolding Ty_def r_def using wfty(1) nm(1) by auto
  from tau_ty wfb have wfabs: "wf_tm N \<Sigma> r (Abs \<tau> b)" by simp
  have szabs: "tm_size (Abs \<tau> b) \<le> r" unfolding r_def by auto
  from Tm_memI[OF szabs wfabs] have "Abs \<tau> b \<in> Tm N \<Sigma> r" .
  then show ?case unfolding r_def .
qed

lemma Tm_exhaust_ex:
  "wf_tm_ty \<Sigma> t \<Longrightarrow> tm_names t \<subseteq> N \<Longrightarrow> \<exists>r. t \<in> Tm N \<Sigma> r"
  using Tm_exhaust by blast

subsection \<open>Sequents over the bounded search space\<close>

text \<open>
  A sequent @{term "(\<Gamma>, c)"} for the bounded search space consists of a (finite, since
  @{term "Tm_wt N \<Sigma> r"} is finite) set of typeable hypotheses @{term \<Gamma>} together with a
  typeable conclusion @{term c}, both drawn from @{term "Tm_wt N \<Sigma> r"}.
\<close>

definition Sequent_r :: "name set \<Rightarrow> hsig \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) set" where
  "Sequent_r N \<Sigma> r = Pow (Tm_wt N \<Sigma> r) \<times> Tm_wt N \<Sigma> r"

lemma finite_Sequent_r: "finite N \<Longrightarrow> finite (Sequent_r N \<Sigma> r)"
  unfolding Sequent_r_def using finite_Tm_wt[of N \<Sigma> r]
  by (intro finite_cartesian_product) (simp_all add: finite_Pow_iff)

end
