theory HOL_Lite_Checker_Completeness
  imports HOL_Lite_Check
begin

section \<open>Completeness of the executable checker\<close>

subsection \<open>Completeness of the type matcher\<close>

lemma tmatch_list_complete_of:
  assumes IH: "\<forall>\<sigma>\<in>set \<sigma>s. \<forall>\<tau> env \<theta>. (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau> \<longrightarrow>
                 (\<exists>env'. tmatch env \<sigma> \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
  shows "\<forall>env \<theta>. (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow>
           (\<exists>env'. tmatch_list env \<sigma>s (map (tsubst \<theta>) \<sigma>s) = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
  using IH
proof (induct \<sigma>s)
  case Nil
  then show ?case by auto
next
  case (Cons s ss)
  from Cons.prems have IHs: "\<forall>\<sigma>\<in>set (s # ss). \<forall>\<tau> (env::(name \<times> ty) list) (\<theta>::name \<Rightarrow> ty). (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau> \<longrightarrow>
                 (\<exists>env'. tmatch env \<sigma> \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
    by simp
  show ?case
  proof (intro allI impI)
    fix env :: "(name \<times> ty) list" and \<theta> :: "name \<Rightarrow> ty"
    assume compat: "\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t"
    from IHs have IHs_hd: "\<forall>\<tau> (env::(name \<times> ty) list) (\<theta>::name \<Rightarrow> ty). (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> s = \<tau> \<longrightarrow>
                 (\<exists>env'. tmatch env s \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
      by simp
    from IHs_hd compat obtain env1 where m1: "tmatch env s (tsubst \<theta> s) = Some env1"
      and compat1: "\<forall>a t. map_of env1 a = Some t \<longrightarrow> \<theta> a = t"
      by blast
    from IHs have IHs_tl: "\<forall>\<sigma>\<in>set ss. \<forall>\<tau> (env::(name \<times> ty) list) (\<theta>::name \<Rightarrow> ty). (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau> \<longrightarrow>
                 (\<exists>env'. tmatch env \<sigma> \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
      by simp
    from Cons.hyps[OF IHs_tl] compat1 obtain env' where m2: "tmatch_list env1 ss (map (tsubst \<theta>) ss) = Some env'"
      and compat': "\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t"
      by blast
    from m1 m2 have "tmatch_list env (s # ss) (map (tsubst \<theta>) (s # ss)) = Some env'" by simp
    with compat' show "\<exists>env'. tmatch_list env (s # ss) (map (tsubst \<theta>) (s # ss)) = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t)"
      by blast
  qed
qed

lemma tmatch_complete:
  "\<forall>\<tau> (env::(name \<times> ty) list) (\<theta>::name \<Rightarrow> ty). (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau> \<longrightarrow>
     (\<exists>env'. tmatch env \<sigma> \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
proof (induct \<sigma> rule: ty.induct)
  case (TyVar a)
  show ?case
  proof (intro allI impI)
    fix \<tau> :: ty and env :: "(name \<times> ty) list" and \<theta> :: "name \<Rightarrow> ty"
    assume compat: "\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t"
      and eq: "tsubst \<theta> (TyVar a) = \<tau>"
    show "\<exists>env'. tmatch env (TyVar a) \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t)"
    proof (cases "map_of env a")
      case (Some \<tau>')
      with compat have "\<theta> a = \<tau>'" by blast
      with eq Some have "\<tau> = \<tau>'" by simp
      with Some compat show ?thesis by auto
    next
      case None
      with eq compat show ?thesis by auto
    qed
  qed
next
  case (TyApp c ss)
  show ?case
  proof (intro allI impI)
    fix \<tau> :: ty and env :: "(name \<times> ty) list" and \<theta> :: "name \<Rightarrow> ty"
    assume compat: "\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t"
      and eq: "tsubst \<theta> (TyApp c ss) = \<tau>"
    from eq have \<tau>: "\<tau> = TyApp c (map (tsubst \<theta>) ss)" by simp
    have IHball: "\<forall>\<sigma>\<in>set ss. \<forall>\<tau> (env::(name \<times> ty) list) (\<theta>::name \<Rightarrow> ty). (\<forall>a t. map_of env a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau> \<longrightarrow>
       (\<exists>env'. tmatch env \<sigma> \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t))"
      using TyApp.hyps by blast
    from tmatch_list_complete_of[OF IHball] compat
    obtain env' where m: "tmatch_list env ss (map (tsubst \<theta>) ss) = Some env'"
      and compat': "\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t"
      by blast
    from m \<tau> have "tmatch env (TyApp c ss) \<tau> = Some env'" by simp
    with compat' show "\<exists>env'. tmatch env (TyApp c ss) \<tau> = Some env' \<and> (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t)"
      by blast
  qed
qed

lemma ty_inst_complete:
  assumes "\<exists>\<theta>. tsubst \<theta> \<sigma>0 = \<tau>"
  shows "ty_inst \<sigma>0 \<tau>"
proof -
  from assms obtain \<theta> where \<theta>: "tsubst \<theta> \<sigma>0 = \<tau>" by blast
  have compat: "\<forall>a t. map_of ([]::(name \<times> ty) list) a = Some t \<longrightarrow> \<theta> a = t" by simp
  from tmatch_complete compat \<theta> obtain env' where "tmatch [] \<sigma>0 \<tau> = Some env'" by blast
  then show ?thesis by (simp add: ty_inst_def)
qed

subsection \<open>Completeness of the type checker\<close>

lemma typeof_complete: "has_type \<Sigma> \<Gamma> t \<tau> \<Longrightarrow> typeof \<Sigma> \<Gamma> t = Some \<tau>"
proof (induction rule: has_type.induct)
  case (Fv \<tau> \<Gamma> x)
  then show ?case by simp
next
  case (Bv i \<Gamma> \<tau>)
  then show ?case by simp
next
  case (Cst c \<sigma>0 \<tau> \<Gamma>)
  from ty_inst_complete[OF Cst.hyps(3)] Cst.hyps(1,2) show ?case by simp
next
  case (App \<Gamma> f \<sigma> \<tau> a)
  then show ?case by simp
next
  case (Abs \<sigma> \<Gamma> b \<tau>)
  then show ?case by simp
qed

subsection \<open>The checker decides typing\<close>

text \<open>
  Combining @{thm typeof_sound} with @{thm typeof_complete} above: the executable checker
  @{const typeof} computes exactly the (unique, by @{thm has_type_unique}) type assigned by
  @{const has_type}, with no side conditions on @{term \<Sigma>} or @{term \<Gamma>} beyond what is already
  built into @{const has_type} itself.
\<close>

theorem typeof_iff_has_type: "typeof \<Sigma> \<Gamma> t = Some \<tau> \<longleftrightarrow> has_type \<Sigma> \<Gamma> t \<tau>"
  using typeof_sound typeof_complete by blast

end
