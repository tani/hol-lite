theory HOL_Lite_Executable_Core
  imports HOL_Lite_Executable_Rules HOL_Lite_Waterfall
begin

section \<open>Locale-free finite search code\<close>

text \<open>The signature and finite axiom enumerator are explicit arguments to the code
  generator; locale interpretations alone do not yield unconditional code equations.\<close>

definition runtime_bounded :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> bool" where
  "runtime_bounded \<Sigma> ns r p =
    (fst p \<subseteq> set (enum_tm ns \<Sigma> r) \<and> snd p \<in> set (enum_tm ns \<Sigma> r))"

definition runtime_scan :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
  ((tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) \<Rightarrow> (tm set \<times> tm) option) \<Rightarrow>
  (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "runtime_scan \<Sigma> ns r f S = concat (map (\<lambda>p1. concat (map (\<lambda>p2.
     case f p1 p2 of None \<Rightarrow> [] | Some q \<Rightarrow> if runtime_bounded \<Sigma> ns r q then [q] else []) S)) S)"

fun runtime_tyvars_ty :: "ty \<Rightarrow> name list" where
  "runtime_tyvars_ty (TyVar a) = [a]"
| "runtime_tyvars_ty (TyApp c ts) = concat (map runtime_tyvars_ty ts)"

fun runtime_tyvars_tm :: "tm \<Rightarrow> name list" where
  "runtime_tyvars_tm (Fv x \<tau>) = runtime_tyvars_ty \<tau>"
| "runtime_tyvars_tm (Bv i) = []"
| "runtime_tyvars_tm (Cst c \<tau>) = runtime_tyvars_ty \<tau>"
| "runtime_tyvars_tm (App f a) = runtime_tyvars_tm f @ runtime_tyvars_tm a"
| "runtime_tyvars_tm (Abs \<tau> b) = runtime_tyvars_ty \<tau> @ runtime_tyvars_tm b"

fun runtime_envs :: "name list \<Rightarrow> ty list \<Rightarrow> (name \<times> ty) list list" where
  "runtime_envs [] tys = [[]]"
| "runtime_envs (v # vs) tys = concat (map (\<lambda>\<tau>.
     map (Cons (v,\<tau>)) (runtime_envs vs tys)) tys)"

definition runtime_vars :: "hsig \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow> (tm set \<times> tm) \<Rightarrow> name list" where
  "runtime_vars \<Sigma> ns r p = remdups (runtime_tyvars_tm (snd p) @
    concat (map runtime_tyvars_tm (filter (\<lambda>t. t \<in> fst p) (enum_tm ns \<Sigma> r))))"

definition runtime_step :: "hsig \<Rightarrow> (name set \<Rightarrow> nat \<Rightarrow> tm list) \<Rightarrow> name list \<Rightarrow> nat \<Rightarrow>
  (tm set \<times> tm) list \<Rightarrow> (tm set \<times> tm) list" where
  "runtime_step \<Sigma> axs ns r S = remdups (
   concat (map (\<lambda>t. case typeof \<Sigma> [] t of
     Some \<tau> \<Rightarrow> (let q = ({}, mk_eq \<tau> t t) in if runtime_bounded \<Sigma> ns r q then [q] else [])
   | None \<Rightarrow> []) (enum_tm ns \<Sigma> r)) @
   concat (map (\<lambda>p. if typeof \<Sigma> [] p = Some boolT \<and>
     runtime_bounded \<Sigma> ns r ({p},p) then [({p},p)] else []) (enum_tm ns \<Sigma> r)) @
   concat (map (\<lambda>w. concat (map (\<lambda>x.
     case w of Abs \<sigma> b \<Rightarrow> (case typeof \<Sigma> [] w of
       Some (TyApp fn [\<sigma>',\<tau>]) \<Rightarrow>
         (let q = ({}, mk_eq \<tau> (App w (Fv x \<sigma>)) (subst_bv 0 (Fv x \<sigma>) b)) in
          if fn = ''fun'' \<and> \<sigma>' = \<sigma> \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
     | _ \<Rightarrow> []) | _ \<Rightarrow> []) ns)) (enum_tm ns \<Sigma> r)) @
   concat (map (\<lambda>p. if runtime_bounded \<Sigma> ns r ({},p) then [({},p)] else []) (axs (set ns) r)) @
   runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
     case (dest_eq (snd p1), dest_eq (snd p2)) of
       (Some (\<tau>,s,t), Some (\<tau>',t',u)) \<Rightarrow>
         if \<tau>' = \<tau> \<and> t' = t then Some (fst p1 \<union> fst p2, mk_eq \<tau> s u) else None
     | _ \<Rightarrow> None) S @
   runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
     case (dest_eq (snd p1), dest_eq (snd p2)) of
       (Some (TyApp fn [\<sigma>0,\<tau>],f,g), Some (\<sigma>,a,b)) \<Rightarrow>
         if fn = ''fun'' \<and> \<sigma>0 = \<sigma>
         then Some (fst p1 \<union> fst p2, mk_eq \<tau> (App f a) (App g b)) else None
     | _ \<Rightarrow> None) S @
   concat (map (\<lambda>p1. concat (map (\<lambda>\<sigma>. concat (map (\<lambda>x.
     case dest_eq (snd p1) of
       Some (\<tau>,s,t) \<Rightarrow>
         (let q = (fst p1, mk_eq (funT \<sigma> \<tau>)
            (Abs \<sigma> (abs_fv 0 x \<sigma> s)) (Abs \<sigma> (abs_fv 0 x \<sigma> t))) in
          if (\<forall>p\<in>fst p1. (x,\<sigma>) \<notin> fvs p) \<and> runtime_bounded \<Sigma> ns r q then [q] else [])
     | None \<Rightarrow> []) (HOL_Lite_Waterfall.fresh_name ns # ns))) (enum_ty ns \<Sigma> r))) S) @
   runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
     case dest_eq (snd p1) of
       Some (\<tau>,p,q) \<Rightarrow> if \<tau> = boolT \<and> snd p2 = p
         then Some (fst p1 \<union> fst p2,q) else None
     | None \<Rightarrow> None) S @
   runtime_scan \<Sigma> ns r (\<lambda>p1 p2.
     Some ((fst p1 - {snd p2}) \<union> (fst p2 - {snd p1}), mk_eq boolT (snd p1) (snd p2))) S @
   concat (map (\<lambda>p1. concat (map (\<lambda>e.
     let \<theta> = (\<lambda>a. case map_of e a of Some t \<Rightarrow> t | None \<Rightarrow> boolT);
         q = (tinst \<theta> ` fst p1, tinst \<theta> (snd p1))
     in if runtime_bounded \<Sigma> ns r q then [q] else [])
     (runtime_envs (runtime_vars \<Sigma> ns r p1) (enum_ty ns \<Sigma> r)))) S))"

context hol_lite_axs
begin

lemma runtime_bounded_eq: "runtime_bounded \<Sigma> ns r p = bounded_seq ns r p"
  by (cases p) (simp add: runtime_bounded_def bounded_seq_def Sequent_r_def set_enum_tm)

lemma runtime_scan_eq: "runtime_scan \<Sigma> ns r f S = scan_pair ns r f S"
  by (simp only: runtime_scan_def scan_pair_def runtime_bounded_eq)

lemma runtime_tyvars_ty_eq: "runtime_tyvars_ty t = tyvar_list t"
proof (induction t rule: ty.induct)
  case (TyVar a)
  then show ?case by simp
next
  case (TyApp c ts)
  have "map runtime_tyvars_ty ts = map tyvar_list ts"
    using TyApp.IH by (intro map_cong) auto
  then show ?case by (simp only: runtime_tyvars_ty.simps tyvar_list.simps)
qed

lemma runtime_tyvars_tm_eq: "runtime_tyvars_tm t = tm_tyvar_list t"
  by (induction t rule: tm.induct) (simp_all add: runtime_tyvars_ty_eq)

lemma runtime_envs_eq: "runtime_envs vs tys = inst_envs vs tys"
  by (induction vs) simp_all

lemma runtime_vars_eq: "runtime_vars \<Sigma> ns r p = inst_var_list ns r p"
  by (simp add: runtime_vars_def inst_var_list_def runtime_tyvars_tm_eq cong: map_cong)

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

lemma runtime_fresh_eq:
  "HOL_Lite_Waterfall.fresh_name ns = fresh_name (set ns)"
  by (simp add: HOL_Lite_Waterfall.fresh_name_def fresh_name_def Max_lengths)

lemma runtime_dest_eq: "HOL_Lite_Waterfall.dest_eq t = dest_eq t"
  by (induction t rule: HOL_Lite_Waterfall.dest_eq.induct)
     (auto simp: dest_eq_def split: tm.splits ty.splits list.splits if_splits)

lemma runtime_step_eq: "runtime_step \<Sigma> axs ns r S = exec_step ns r S"
  unfolding runtime_step_def exec_step_def
    exec_refl_def exec_assm_def exec_beta_def exec_axiom_def
    exec_trans_def exec_mk_comb_def exec_abs_def exec_eq_mp_def
    exec_deduct_antisym_def exec_inst_type_def
  by (simp only: runtime_scan_eq runtime_bounded_eq runtime_envs_eq
      runtime_vars_eq runtime_fresh_eq runtime_dest_eq)

lemma set_runtime_step:
  "set S \<subseteq> Sequent_r (set ns) \<Sigma> r \<Longrightarrow>
   set (runtime_step \<Sigma> axs ns r S) = step_r (set ns) r (set S)"
  by (simp add: runtime_step_eq set_exec_step)

end
end
