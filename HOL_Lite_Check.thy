theory HOL_Lite_Check
  imports HOL_Lite_Typing
begin

section \<open>An executable type checker\<close>

text \<open>
  @{const has_type} is a specification, not an algorithm: the @{text Cst} rule only demands the
  existence of a type substitution, and @{text Bv}/@{text App} are not syntax-directed on the
  result type.  This theory defines an executable checker @{term typeof} that computes the
  (unique, by @{thm has_type_unique}) type of a term, backed by a one-way, syntax-directed type
  matcher @{term tmatch}.  Only soundness (@{text "typeof \<Sigma> \<Gamma> t = Some \<tau> \<Longrightarrow> has_type \<Sigma> \<Gamma> t \<tau>"}) is
  proved; completeness is not needed for the waterfall processors built on top of this theory.
\<close>

subsection \<open>A one-way type matcher\<close>

text \<open>
  @{term "tmatch env \<sigma> \<tau>"} tries to match the pattern @{term \<sigma>} against the (ground) target
  @{term \<tau>}, extending the association-list environment @{term env} of already-bound type
  variables.  A type variable already bound in @{term env} must match the same type again; an
  unbound one is bound to whatever it faces.  @{term tmatch_list} is the analogous matcher for
  argument lists of a type constructor.  The environment only ever grows by prepending fresh
  bindings, never by overwriting an existing one -- this is what makes the soundness proof below
  go through by simple extension reasoning.
\<close>

fun tmatch :: "(name \<times> ty) list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (name \<times> ty) list option"
  and tmatch_list :: "(name \<times> ty) list \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> (name \<times> ty) list option" where
  "tmatch env (TyVar a) \<tau> =
     (case map_of env a of
        Some \<tau>' \<Rightarrow> if \<tau>' = \<tau> then Some env else None
      | None \<Rightarrow> Some ((a, \<tau>) # env))"
| "tmatch env (TyApp c ss) \<tau> =
     (case \<tau> of
        TyApp d ts \<Rightarrow> if c = d then tmatch_list env ss ts else None
      | TyVar _ \<Rightarrow> None)"
| "tmatch_list env [] \<tau>s = (if \<tau>s = [] then Some env else None)"
| "tmatch_list env (\<sigma> # \<sigma>s) \<tau>s =
     (case \<tau>s of
        [] \<Rightarrow> None
      | \<tau> # \<tau>s' \<Rightarrow> (case tmatch env \<sigma> \<tau> of Some env' \<Rightarrow> tmatch_list env' \<sigma>s \<tau>s' | None \<Rightarrow> None))"

text \<open>
  Two invariants of a successful match, proved simultaneously by function induction: the
  returned environment extends the input one, and it makes any total substitution extending it
  witness the match, i.e. instantiate the pattern to the target.
\<close>

lemma tmatch_extends_and_sound:
  "\<And>env'. tmatch env \<sigma> \<tau> = Some env' \<Longrightarrow>
     (\<forall>a t. map_of env a = Some t \<longrightarrow> map_of env' a = Some t) \<and>
     (\<forall>\<theta>. (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau>)"
  and tmatch_list_extends_and_sound:
  "\<And>env'. tmatch_list env \<sigma>s \<tau>s = Some env' \<Longrightarrow>
     (\<forall>a t. map_of env a = Some t \<longrightarrow> map_of env' a = Some t) \<and>
     (\<forall>\<theta>. (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> map (tsubst \<theta>) \<sigma>s = \<tau>s)"
proof (induction env \<sigma> \<tau> and env \<sigma>s \<tau>s rule: tmatch_tmatch_list.induct)
  case (1 env a \<tau> env')
  show ?case
  proof (intro conjI)
    show "\<forall>b t. map_of env b = Some t \<longrightarrow> map_of env' b = Some t"
    proof (cases "map_of env a")
      case (Some \<tau>')
      with "1.prems" have "\<tau>' = \<tau> \<and> env' = env" by (auto split: if_splits)
      then show ?thesis by simp
    next
      case None
      with "1.prems" have env': "env' = (a, \<tau>) # env" by simp
      show ?thesis
      proof (intro allI impI)
        fix b t assume "map_of env b = Some t"
        with None have "b \<noteq> a" by auto
        with env' \<open>map_of env b = Some t\<close> show "map_of env' b = Some t" by simp
      qed
    qed
  next
    show "\<forall>\<theta>. (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> (TyVar a) = \<tau>"
    proof (intro allI impI)
      fix \<theta> assume \<theta>: "\<forall>b t. map_of env' b = Some t \<longrightarrow> \<theta> b = t"
      show "tsubst \<theta> (TyVar a) = \<tau>"
      proof (cases "map_of env a")
        case (Some \<tau>')
        with "1.prems" have "\<tau>' = \<tau> \<and> env' = env" by (auto split: if_splits)
        with Some \<theta> show ?thesis by simp
      next
        case None
        with "1.prems" have "env' = (a, \<tau>) # env" by simp
        with \<theta> show ?thesis by simp
      qed
    qed
  qed
next
  case (2 env c ss \<tau> env')
  from "2.prems" obtain d ts where \<tau>: "\<tau> = TyApp d ts" and cd: "c = d"
    and m: "tmatch_list env ss ts = Some env'"
    by (cases \<tau>) (auto split: if_splits)
  from "2.IH"[OF \<tau> cd m]
  show ?case by (auto simp: \<tau> cd)
next
  case (3 env \<tau>s env')
  then show ?case by (auto split: if_splits)
next
  case (4 env \<sigma> \<sigma>s \<tau>s env')
  from "4.prems" obtain \<tau> \<tau>s' env1 where \<tau>s: "\<tau>s = \<tau> # \<tau>s'"
    and m1: "tmatch env \<sigma> \<tau> = Some env1"
    and m2: "tmatch_list env1 \<sigma>s \<tau>s' = Some env'"
    by (cases \<tau>s) (auto split: option.splits)
  from "4.IH"(1)[OF \<tau>s m1] have IH1: "(\<forall>a t. map_of env a = Some t \<longrightarrow> map_of env1 a = Some t) \<and>
     (\<forall>\<theta>. (\<forall>a t. map_of env1 a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> tsubst \<theta> \<sigma> = \<tau>)" .
  from "4.IH"(2)[OF \<tau>s m1 m2] have IH2: "(\<forall>a t. map_of env1 a = Some t \<longrightarrow> map_of env' a = Some t) \<and>
     (\<forall>\<theta>. (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> map (tsubst \<theta>) \<sigma>s = \<tau>s')" .
  show ?case
  proof (intro conjI)
    from IH1 IH2 show "\<forall>a t. map_of env a = Some t \<longrightarrow> map_of env' a = Some t" by blast
  next
    show "\<forall>\<theta>. (\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t) \<longrightarrow> map (tsubst \<theta>) (\<sigma> # \<sigma>s) = \<tau>s"
    proof (intro allI impI)
      fix \<theta> assume \<theta>: "\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t"
      from IH2 \<theta> have tl: "map (tsubst \<theta>) \<sigma>s = \<tau>s'" by blast
      from IH2 \<theta> have "\<forall>a t. map_of env1 a = Some t \<longrightarrow> \<theta> a = t" by blast
      with IH1 have hd: "tsubst \<theta> \<sigma> = \<tau>" by blast
      from hd tl \<tau>s show "map (tsubst \<theta>) (\<sigma> # \<sigma>s) = \<tau>s" by simp
    qed
  qed
qed

lemma tmatch_sound:
  assumes "tmatch env \<sigma> \<tau> = Some env'"
    and "\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t"
  shows "tsubst \<theta> \<sigma> = \<tau>"
  using tmatch_extends_and_sound[OF assms(1)] assms(2) by blast

subsection \<open>Matching against the empty environment\<close>

text \<open>
  @{term "ty_inst \<sigma>0 \<tau>"} decides whether @{term \<tau>} is an instance of the (generic) pattern
  @{term \<sigma>0}, by matching from the empty environment.
\<close>

definition ty_inst :: "ty \<Rightarrow> ty \<Rightarrow> bool" where
  "ty_inst \<sigma>0 \<tau> = (tmatch [] \<sigma>0 \<tau> \<noteq> None)"

lemma ty_inst_sound: "ty_inst \<sigma>0 \<tau> \<Longrightarrow> \<exists>\<theta>. tsubst \<theta> \<sigma>0 = \<tau>"
proof -
  assume "ty_inst \<sigma>0 \<tau>"
  then obtain env' where m: "tmatch [] \<sigma>0 \<tau> = Some env'"
    by (auto simp: ty_inst_def)
  define \<theta> where "\<theta> = (\<lambda>a. case map_of env' a of Some t \<Rightarrow> t | None \<Rightarrow> TyVar a)"
  have "\<forall>a t. map_of env' a = Some t \<longrightarrow> \<theta> a = t" by (simp add: \<theta>_def)
  with tmatch_sound[OF m] have "tsubst \<theta> \<sigma>0 = \<tau>" by blast
  then show ?thesis by blast
qed

subsection \<open>The type checker\<close>

text \<open>
  @{term "typeof \<Sigma> \<Gamma> t"} computes the type of @{term t} under the loose-index context @{term \<Gamma>},
  or fails.  It is syntax-directed on @{term t} and mirrors the rules of @{const has_type}
  exactly, using @{const ty_inst} in place of the existential side condition of the @{text Cst}
  rule.
\<close>

fun typeof :: "hsig \<Rightarrow> ty list \<Rightarrow> tm \<Rightarrow> ty option" where
  "typeof \<Sigma> \<Gamma> (Fv x \<tau>) = (if wf_ty \<Sigma> \<tau> then Some \<tau> else None)"
| "typeof \<Sigma> \<Gamma> (Bv i) = (if i < length \<Gamma> then Some (\<Gamma> ! i) else None)"
| "typeof \<Sigma> \<Gamma> (Cst c \<tau>) =
     (case ctype \<Sigma> c of
        None \<Rightarrow> None
      | Some \<sigma>0 \<Rightarrow> if wf_ty \<Sigma> \<tau> \<and> ty_inst \<sigma>0 \<tau> then Some \<tau> else None)"
| "typeof \<Sigma> \<Gamma> (App f a) =
     (case typeof \<Sigma> \<Gamma> f of
        Some (TyApp c [\<sigma>, \<tau>]) \<Rightarrow>
          if c = ''fun'' then
            (case typeof \<Sigma> \<Gamma> a of
               Some \<sigma>' \<Rightarrow> if \<sigma>' = \<sigma> then Some \<tau> else None
             | None \<Rightarrow> None)
          else None
      | _ \<Rightarrow> None)"
| "typeof \<Sigma> \<Gamma> (Abs \<sigma> b) =
     (if wf_ty \<Sigma> \<sigma> then
        (case typeof \<Sigma> (\<sigma> # \<Gamma>) b of Some \<tau> \<Rightarrow> Some (funT \<sigma> \<tau>) | None \<Rightarrow> None)
      else None)"

lemma typeof_sound: "typeof \<Sigma> \<Gamma> t = Some \<tau> \<Longrightarrow> has_type \<Sigma> \<Gamma> t \<tau>"
proof (induction t arbitrary: \<Gamma> \<tau>)
  case (Fv x \<sigma>)
  then show ?case by (auto split: if_splits intro: has_type.Fv)
next
  case (Bv i)
  then show ?case by (auto split: if_splits intro: has_type.Bv)
next
  case (Cst c \<sigma>)
  from Cst.prems obtain \<sigma>0 where c: "ctype \<Sigma> c = Some \<sigma>0" and wf: "wf_ty \<Sigma> \<sigma>"
    and inst: "ty_inst \<sigma>0 \<sigma>" and \<tau>: "\<tau> = \<sigma>"
    by (auto split: option.splits if_splits)
  from ty_inst_sound[OF inst] obtain \<theta> where "tsubst \<theta> \<sigma>0 = \<sigma>" by blast
  with c wf \<tau> show ?case by (auto intro: has_type.Cst)
next
  case (App f a)
  from App.prems obtain c \<sigma> \<rho> where
    f: "typeof \<Sigma> \<Gamma> f = Some (TyApp c [\<sigma>, \<rho>])" and cfun: "c = ''fun''"
    and a: "typeof \<Sigma> \<Gamma> a = Some \<sigma>" and \<tau>: "\<tau> = \<rho>"
    by (auto split: option.splits ty.splits list.splits if_splits)
  from f cfun have f': "typeof \<Sigma> \<Gamma> f = Some (funT \<sigma> \<rho>)" by simp
  from App.IH(1)[OF f'] have hf: "has_type \<Sigma> \<Gamma> f (funT \<sigma> \<rho>)" .
  from App.IH(2)[OF a] have ha: "has_type \<Sigma> \<Gamma> a \<sigma>" .
  from has_type.App[OF hf ha] \<tau> show ?case by simp
next
  case (Abs \<sigma> b)
  from Abs.prems obtain \<tau>0 where wf: "wf_ty \<Sigma> \<sigma>" and b: "typeof \<Sigma> (\<sigma> # \<Gamma>) b = Some \<tau>0"
    and \<tau>: "\<tau> = funT \<sigma> \<tau>0"
    by (auto split: if_splits option.splits)
  from Abs.IH[OF b] have "has_type \<Sigma> (\<sigma> # \<Gamma>) b \<tau>0" .
  with wf \<tau> show ?case by (simp add: has_type.Abs)
qed

end
