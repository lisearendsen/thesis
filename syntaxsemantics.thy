(*
    Author: Lise Arendsen, TU/e
*)

section \<open>Results on the syntax and semantics of the modal $\mu$-calculus\<close>

theory syntaxsemantics
imports Main "Regular-Sets.Regular_Exp" "HOL-Library.Omega_Words_Fun"
begin

subsection \<open>Auxiliary results\<close>

notation Atom ("{_}\<^sub>R" 85)
notation Plus (infixl "+\<^sub>R" 80)
notation Times (infixl "\<cdot>" 80)
notation Star ("_\<^sup>\<star>" 80)

text \<open>We extend \<open>rexp\<close> by adding a constructor \<open>Acts\<close>, representing a set of actions.
In this way regular expressions are inherently finite\<close>

fun Actslist :: "'a list \<Rightarrow> 'a rexp " where
"Actslist [] = Zero" |           
"Actslist (a # as) = {a}\<^sub>R +\<^sub>R (Actslist as)"

definition Acts :: "'a set \<Rightarrow> 'a rexp" where
"Acts A = Actslist (if finite A then (SOME listA. set listA = A) else undefined)"

lemma Actslistlang : "lang (Actslist A) =  {[a] |a. a \<in> set A}"
  by (induct A; auto)

lemma Actslang [simp] : "finite A \<Longrightarrow> lang (Acts A) =  {[a] |a. a \<in> A}"
  apply (simp add: Acts_def Actslistlang)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma abinconc : "a \<in> A \<and> b \<in> B \<Longrightarrow> a@b \<in> A@@B"
  using concat_def by blast

lemma exists_abinconc : "(ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> a \<in> A \<and> b \<in> B)"
  by blast

lemma exists_map_abinconc : "(map f ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> (map f a) \<in> A \<and> (map f b) \<in> B)"
  apply (rule iffI)
  apply (metis exists_abinconc append_eq_map_conv)
  apply (metis abinconc map_append)
  done

lemma negcupcap : "-\<Union> {S'. P S'} = \<Inter> {S'. P (-S')}"
  apply auto
proof-
  fix s S'
  assume assum1: "\<forall>S'. P (-S') \<longrightarrow> s \<in> S'"
  assume assum2: "s \<in> S'"
  assume "P S'"
  hence "P (-(-S'))" by auto
  hence "s \<in> -S'" using assum1 by blast
  thus False using assum2 by auto
qed

subsection \<open>Defining the $\mu$-calculus\<close>

text \<open>A $\mu$-calculus formula is defined on a type of actions \<open>'a\<close>,
and de Bruijn indices are used as variables.\<close>

datatype 'a formula =
  tt | ff | var nat |
  neg "'a formula" ("\<not>\<^sub>\<mu>_" [75] 75)|
  and' "'a formula" "'a formula" (infixl "\<and>\<^sub>\<mu>" 70) | 
  or "'a formula" "'a formula" (infixl "\<or>\<^sub>\<mu>" 70) | 
  box 'a "'a formula" ("[_]\<^sub>\<mu>_" [80, 80] 80) |
  diamond 'a "'a formula" ("\<langle>_\<rangle>\<^sub>\<mu>_" [80, 80] 80) |
  nu "'a formula" ("\<nu> _" [65] 65)|
  mu "'a formula" ("\<mu> _" [65] 65)

abbreviation implies :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infix "\<Longrightarrow>\<^sub>R" 70) where
  "f \<Longrightarrow>\<^sub>R g \<equiv> \<not>\<^sub>\<mu>f \<or>\<^sub>\<mu> g"

datatype example_states = s\<^sub>0 | s\<^sub>1 | s\<^sub>2
datatype example_actions = \<a> | \<b> | \<c>

value "\<not>\<^sub>\<mu>(var 0 \<and>\<^sub>\<mu> tt) :: example_actions formula"
value "\<langle>\<b>\<rangle>\<^sub>\<mu>[\<a>]\<^sub>\<mu>tt :: example_actions formula"
value "\<mu> var 0 \<and>\<^sub>\<mu> (\<langle>\<b>\<rangle>\<^sub>\<mu>[\<a>]\<^sub>\<mu>tt) :: example_actions formula"

value "diamond \<b> (box \<a> tt) :: example_actions formula"
value "nu (var 0) :: example_actions formula "

text \<open>Similarly a labeled transition system is defined on a type of actions \<open>'a\<close> 
and a type of states \<open>'s\<close> (instead of a set of actions and a set of states).
A labeled transition system then consists of a set of transitions.\<close>

record ('a, 's) lts =
transition :: "('s \<times> 'a \<times> 's) set"

text \<open>A record can be instantiated as follows.\<close>

definition example_lts :: "(example_actions, example_states) lts" where
"example_lts \<equiv> \<lparr>transition = {(s\<^sub>0, \<c>, s\<^sub>0), (s\<^sub>0, \<b>, s\<^sub>1), (s\<^sub>0, \<b>, s\<^sub>2), (s\<^sub>1, \<a>, s\<^sub>0), (s\<^sub>1, \<a>, s\<^sub>1),
  (s\<^sub>1, \<c>, s\<^sub>2), (s\<^sub>2, \<b>, s\<^sub>1) }\<rparr>"

text \<open>An environment is updated by shifting all variable mappings to the right, i.e.
\<open>newenvironment e S' (Suc i) = e i\<close>.\<close>

abbreviation newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S' \<equiv> S' ## e"

text \<open>Some simplifications for \<open>newenvironment\<close>, specifically with respect to updating the new environment.\<close>

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S')((Suc i) := -((newenvironment e S') (Suc i))) = newenvironment (e(i := -e i)) S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S')(0 := (-(newenvironment e S') 0)) = newenvironment e (-S')"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchsuccessor [simp] : 
"newenvironment (e(i :=  S')) S'' = (newenvironment e S'')((Suc i) := S')"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchzero [simp] : 
"(newenvironment e S'')(0 := S') = newenvironment e S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

text \<open>With the definition of \<open>newenvironment\<close>, we define the semantics of formulas.\<close>

fun formulasemantics :: "'a formula  \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk> _ _" [60, 80, 80] 80)
where 
  "\<lbrakk>tt\<rbrakk> M e = UNIV " |
  "\<lbrakk>ff\<rbrakk> M e =  {}" |
  "\<lbrakk>var X\<rbrakk> M e  = e X" |
  "\<lbrakk>neg f\<rbrakk> M e = -(\<lbrakk>f\<rbrakk> M e)" |
  "\<lbrakk>and' f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<inter> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>or f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<union> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>diamond act f\<rbrakk> M e = {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>box act f\<rbrakk> M e = {s. \<forall>s'. (s, act, s') \<in> transition M \<longrightarrow> s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>nu f\<rbrakk> M e = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" |
  "\<lbrakk>mu f\<rbrakk> M e = \<Inter> {S'. S' \<supseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}"

text \<open>We can prove the evaluation of semantics of formulas on the example as given before.\<close>

lemma "\<lbrakk>[\<a>]\<^sub>\<mu>ff\<rbrakk> example_lts e = {s\<^sub>0, s\<^sub>2}"
  apply (simp add: example_lts_def)
  using example_states.exhaust apply auto
  done

lemma "\<lbrakk>\<nu> \<langle>\<a>\<rangle>\<^sub>\<mu>var 0\<rbrakk> example_lts e = {s\<^sub>1}"
proof-
  have "\<forall>S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'} = (S' = {} \<or> S' = {s\<^sub>1})" using example_states.exhaust by auto
  hence "\<Union> {S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'}} = {s\<^sub>1}" by auto
  thus ?thesis by (simp add: example_lts_def)
qed

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
  apply (simp add: example_lts_def)
  apply (rule equalityI)
  apply blast
  apply (rule Union_upper)
  apply auto
  done

subsection \<open>Functions and extensions over formulas\<close>

text \<open>\<open>shiftup\<close> is defined on formulas to be able to wrap a formula in a new binder 
without changing its definition. For example, \<open>var 0\<close> and \<open>mu (var 1)\<close> represent the same formula.
\<open>shiftdown\<close> is its opposite.\<close>

fun shiftup :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "shiftup tt i = tt " |
  "shiftup ff i = ff" |
  "shiftup (var X) i  = (if X < i then var X else var (X + 1))" |
  "shiftup (neg f) i = neg (shiftup f i)" |
  "shiftup (and' f f') i = and' (shiftup f i) (shiftup f' i) " |
  "shiftup (or f f') i = or (shiftup f i) (shiftup f' i)" |
  "shiftup (box act f) i = box act (shiftup f i)" |
  "shiftup (diamond act f) i = diamond act (shiftup f i)" | 
  "shiftup (nu f) i = nu (shiftup f (Suc i))" |
  "shiftup (mu f) i = mu (shiftup f (Suc i))"

fun shiftdown :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "shiftdown tt i = tt " |
  "shiftdown ff i = ff" |
  "shiftdown (var X) i  = (if X \<le> i then var X else var (X - 1))" |
  "shiftdown (neg f) i = neg (shiftdown f i)" |
  "shiftdown (and' f f') i = and' (shiftdown f i) (shiftdown f' i) " |
  "shiftdown (or f f') i = or (shiftdown f i) (shiftdown f' i)" |
  "shiftdown (diamond act f) i = diamond act (shiftdown f i) " |
  "shiftdown (box act f) i = box act (shiftdown f i)" |
  "shiftdown (nu f) i = nu (shiftdown f (Suc i))" |
  "shiftdown (mu f) i = mu (shiftdown f (Suc i))"

lemma shiftupanddown : "shiftdown (shiftup f i) i = f"
  by (induct f arbitrary : i; simp)

definition shiftdownenv :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"shiftdownenv e i n = (if n < i then e n else e (n + 1))"

lemma shiftdownnewenv_eq_newenvshiftdown [simp] : "shiftdownenv (newenvironment e S') (Suc i) = newenvironment (shiftdownenv e i) S'"
  by (rule; induct_tac x; simp add: shiftdownenv_def)

lemma shiftdownnewenvzero_eq_newenv [simp] : "shiftdownenv (newenvironment e S') 0 = e"
  by (rule; induct_tac x; simp add: shiftdownenv_def)

lemma switchnewenvironmentshiftdown : "\<lbrakk>shiftdown f (Suc i)\<rbrakk> M (newenvironment (shiftdownenv e i) S') = 
  \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))"
  by simp

definition envrepeati :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"envrepeati e i \<equiv> conc (prefix (Suc i) e) (suffix i e)"

lemma envrepeatidef :  "envrepeati e i = (\<lambda>j. if j > Suc i then e (j - Suc 0) else (if j \<le> i then e j else e i))"
proof
  fix j
  {
    assume assum1 : "Suc i < j"
    hence "\<not>j < length (prefix (Suc i) e)" by simp
    hence "conc (prefix (Suc i) e) (suffix i e) j = suffix i e (j - length (prefix (Suc i) e))" using conc_snd by metis
    hence "conc (prefix (Suc i) e) (suffix i e) j = e (j - Suc 0)" using assum1 by simp
  }
  moreover {
    assume "j \<le> i"
    hence "j < length (prefix (Suc i) e)" by auto
    hence "conc (prefix (Suc i) e) (suffix i e) j = e j" using prefix_suffix conc_fst by metis
  }
  moreover {
    assume "\<not>Suc i < j"
    moreover assume "\<not>j \<le> i"
    ultimately have "j = Suc i" by auto
    hence "conc (prefix (Suc i) e) (suffix i e) j = e i" by auto
  }
  ultimately show "envrepeati e i j = (if Suc i < j then e (j - Suc 0) else if j \<le> i then e j else e i)" using envrepeati_def by metis
qed

lemma newenvenvrepeatswitch : "newenvironment (envrepeati e i) S' = envrepeati (newenvironment e S') (Suc i)"
  apply rule
  apply (induct_tac x; simp add: envrepeatidef)
proof (rule impI)+
  fix n
  assume "Suc i < n"
  hence "n > Suc 0" by auto
  thus "e (n - Suc 0) = newenvironment e S' n" by (induct n; simp)
qed

lemma shiftdownenvrepeat : "\<lbrakk>shiftdown f i\<rbrakk> M e = \<lbrakk>f\<rbrakk> M (envrepeati e i)"
  apply (induct f arbitrary: e i; simp add: shiftdownenv_def newenvenvrepeatswitch)
  apply (simp add: envrepeatidef)
  apply (intro impI)
  apply (subgoal_tac "x = Suc i"; auto)
  done

lemma shiftdownnewenv : "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>shiftdown f 0\<rbrakk> M e "
  apply (subgoal_tac "envrepeati e 0 = newenvironment e (e 0)")
  apply (simp add: shiftdownenvrepeat)
  apply rule
  apply (induct_tac x; simp add: envrepeati_def)
  done

text \<open>Defining extensions of the mu calculus, specifically \<open>And\<close>, \<open>Or\<close>, \<open>Diamond\<close>, and \<open>Box\<close>.\<close>

fun Andlist :: "'b list \<Rightarrow> ('b \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"Andlist [] F = tt" |
"Andlist (a # as) F = and' (F a) (Andlist as F)"

definition And :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"And A F = Andlist (if finite A then (SOME listA. set listA = A) else undefined) F"

definition Or :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"Or A F = neg (And A (\<lambda>a. neg (F a)))"

syntax
  "_And" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool" ("(\<open>indent=3 notation=\<open>binder \<And>\<^sub>\<mu>\<close>\<close>\<And>\<^sub>\<mu>(_/\<in>_)./ _)" [70, 70, 70] 70)
  "_Or" :: "pttrn \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool" ("(\<open>indent=3 notation=\<open>binder \<Or>\<^sub>\<mu>\<close>\<close>\<Or>\<^sub>\<mu>(_/\<in>_)./ _)" [70, 70, 70] 70)

translations
  "\<And>\<^sub>\<mu> T \<in> \<T>. P" \<rightleftharpoons> "CONST And \<T> (\<lambda>T. P)"
  "\<Or>\<^sub>\<mu> T \<in> \<T>. P" \<rightleftharpoons> "CONST Or \<T> (\<lambda>T. P)"

lemma Andlist_eq_all : "\<lbrakk>Andlist Alist F\<rbrakk> M e = {s. \<forall>a \<in> set Alist. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (induct Alist; simp; auto)

lemma And_eq_all : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = {s. \<forall>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  apply (simp add: And_def Andlist_eq_all)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma And_eq_all' [simp] : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = (\<Inter>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst And_eq_all; auto)

lemma Or_eq_exist : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = {s. \<exists>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (auto simp: Or_def)

lemma Or_eq_exist' [simp] : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = (\<Union>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst Or_eq_exist; auto)

notation Atom ("{_}\<^sub>R" 85)
notation Plus (infixl "+\<^sub>R" 80)
notation Times (infixl "\<cdot>" 80)
notation Star ("_\<^sup>\<star>" 80)

fun Diamond :: "'a rexp \<Rightarrow> 'a formula \<Rightarrow> 'a formula " ("\<langle>_\<rangle>\<^sub>R _" [80, 80] 80) where 
"Diamond Zero f = ff" |
"Diamond One f = f" |
"Diamond (Atom a) f = diamond a f" |
"Diamond (Plus R Q) f = or (Diamond R f) (Diamond Q f)" |
"Diamond (Times R Q) f = Diamond R (Diamond Q f)" |
"Diamond (Star R) f =  mu (or (Diamond R (var 0)) (shiftup f 0))" 

lemma Diamondlist_eq_exist [simp] : 
"\<lbrakk>Diamond (Actslist A) f\<rbrakk> M e = {s. \<exists>s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; auto)

lemma Diamond_eq_exist [simp] : "finite A \<Longrightarrow>
\<lbrakk>Diamond (Acts A) f\<rbrakk> M e = {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Acts_def)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftuptwice : "m \<le> i \<Longrightarrow> shiftup (shiftup f m) (Suc i) = shiftup (shiftup f i) m"
  by (induct f arbitrary : i m; simp)

lemma shiftupDiamond [simp] : "shiftup (Diamond R f) i = Diamond R (shiftup f i)"
  by (induct R arbitrary : i f; simp add: shiftuptwice)

lemma shiftupdown : "m \<le> i \<Longrightarrow> shiftdown (shiftup f m) (Suc i) = shiftup (shiftdown f i) m"
  by (induct f arbitrary : i m; simp; arith)

lemma shiftdownDiamond [simp] : "shiftdown (Diamond R f) i = Diamond R (shiftdown f i)"
  by (induct R arbitrary : i f; simp add: shiftupdown)

fun Box :: "'a rexp \<Rightarrow> 'a formula \<Rightarrow> 'a formula" ("[_]\<^sub>R _" [80, 80] 80) where 
"Box Zero f = tt" |
"Box One f = f" |
"Box (Atom a) f = box a f" |
"Box (Plus R Q) f = and' (Box R f) (Box Q f)" |
"Box (Times R Q) f = Box R (Box Q f)" |
"Box (Star R) f =  nu (and' (Box R (var 0)) (shiftup f 0))" 

lemma Boxlist_eq_forall [simp] : "\<lbrakk>Box (Actslist A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; auto)

lemma Box_eq_forall [simp] : "finite A \<Longrightarrow>
\<lbrakk>Box (Acts A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Acts_def)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftupBox [simp] : "shiftup (Box R f) i = Box R (shiftup f i)"
  by (induct R arbitrary : i f; simp add: shiftuptwice)

lemma shiftdownBox [simp] : "shiftdown (Box R f) i = Box R (shiftdown f i)"
  by (induct R arbitrary : i f; simp add: shiftupdown)

text \<open>Defining \<open>negvar\<close> to prove duality of mu and nu, and also proving how the definition can 
be unfolded on our extensions.\<close>

fun negvar :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "negvar tt i = tt " |
  "negvar ff i = ff" |
  "negvar (var X) i  = (if i = X then neg (var X) else var X)" |
  "negvar (neg f) i = neg (negvar f i)" |
  "negvar (and' f f') i = and' (negvar f i) (negvar f' i) " |
  "negvar (or f f') i = or (negvar f i) (negvar f' i)" |
  "negvar (box a f) i = box a (negvar f i)" |
  "negvar (diamond a f) i = diamond a (negvar f i) " |
  "negvar (nu f) i = nu (negvar f (Suc i))" |
  "negvar (mu f) i = mu (negvar f (Suc i))"

lemma negvarshiftup : "m \<le> i \<Longrightarrow> negvar (shiftup f m) (Suc i) = shiftup (negvar f i) m"
  by (induct f arbitrary : m i; simp)

lemma negvarDiamond [simp] : "negvar (Diamond R f) i = Diamond R (negvar f i)"
  by (induct R arbitrary : f i; simp add : negvarshiftup)

lemma negvarBox [simp] : "negvar (Box R f) i = Box R (negvar f i)"
  by (induct R arbitrary : f i; simp add : negvarshiftup)

lemma negvarAndlist [simp] : "negvar (Andlist Alist F) i = Andlist Alist (\<lambda>a. (negvar (F a) i))"
  by (induct Alist; simp)

lemma negvarAnd [simp] : "finite A \<Longrightarrow> negvar (And A F) i = And A (\<lambda>a. (negvar (F a) i))"
  by (simp add: And_def)

lemma negvarOr [simp] : "finite A \<Longrightarrow> negvar (Or A F) i = Or A (\<lambda>a. (negvar (F a) i))"
  by (simp add: Or_def)

value "negvar (or (var 0) (mu (and' (var 0) (var 1)))) 0 :: nat formula"

subsubsection \<open>Duality of formulas\<close>

lemma negformula : "s \<in> \<lbrakk>neg f\<rbrakk> M e \<longleftrightarrow> s \<notin> \<lbrakk>f\<rbrakk> M e" 
  by simp

lemma negtrue : "\<lbrakk>neg tt\<rbrakk> M e = \<lbrakk>ff\<rbrakk> M e"
  by simp

lemma negfalse : "\<lbrakk>neg ff\<rbrakk> M e = \<lbrakk>tt\<rbrakk> M e"
  by simp

lemma negnegf : "\<lbrakk>neg (neg (f))\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by simp

lemma negand' : "\<lbrakk>neg (and' f f')\<rbrakk> M e = \<lbrakk>or (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negAnd : "finite A \<Longrightarrow> \<lbrakk>neg (And A F)\<rbrakk> M e = \<lbrakk>Or A (\<lambda>a. neg (F a))\<rbrakk> M e"
  by auto

lemma negor : "\<lbrakk>neg (or f f')\<rbrakk> M e = \<lbrakk>and' (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negOr : "\<lbrakk>neg (Or A F)\<rbrakk> M e = \<lbrakk>And A (\<lambda>a. neg (F a))\<rbrakk> M e"
  by (simp add: Or_def)

lemma negbox : "\<lbrakk>neg (box a f)\<rbrakk> M e = \<lbrakk>diamond a (neg f)\<rbrakk> M e"
  by auto

lemma negdiamond : "\<lbrakk>neg (diamond a f)\<rbrakk> M e = \<lbrakk>box a (neg f)\<rbrakk> M e"
  by auto

lemma movenegvarin : "\<lbrakk>f\<rbrakk> M e(i := -e(i)) = \<lbrakk>negvar f i\<rbrakk> M e"
  apply (induct f arbitrary : e i; simp; subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := -e i) = \<lbrakk>negvar f (Suc i)\<rbrakk> M (newenvironment e S')")
  apply simp_all
proof-
  fix f e i S'
  assume "\<And>e i. \<lbrakk>f\<rbrakk> M e(i := -e i) = \<lbrakk>negvar f i\<rbrakk> M e"
  hence "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := -(newenvironment e S' (Suc i)))) = \<lbrakk>negvar f (Suc i)\<rbrakk> M (newenvironment e S')" by metis
  moreover have "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := -(newenvironment e S' (Suc i)))) = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := -e i))" by simp
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := -e i) = \<lbrakk>negvar f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
  thus " \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := -e i) = \<lbrakk>negvar f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
qed

lemma negnu : "\<lbrakk>neg (nu f)\<rbrakk> M e = \<lbrakk>mu (neg (negvar f 0))\<rbrakk> M e"
proof-
  have "\<And> S'. \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S')) = \<lbrakk>negvar (neg f) 0\<rbrakk> M (newenvironment e S')" using movenegvarin newenvironmentzerocomplement by metis  
  hence "\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))} = \<Inter> {S'. S' \<supseteq> \<lbrakk>neg (negvar f 0)\<rbrakk> M (newenvironment e S')}" by auto
  moreover have "\<lbrakk>neg (nu f)\<rbrakk> M e = (\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))})" by (auto simp: negcupcap)
  ultimately show ?thesis by auto
qed  

lemma negvarnegvar [simp] : "\<lbrakk>negvar (negvar f i) i\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  (*by (metis (mono_tags, opaque_lifting)
      boolean_algebra_class.boolean_algebra.double_compl fun_upd_def fun_upd_triv
      fun_upd_upd movenegvarin)*)
  by (induct f arbitrary : i e; simp)

lemma negmu : "\<lbrakk>neg (mu f)\<rbrakk> M e = \<lbrakk>nu (neg (negvar f 0))\<rbrakk> M e"
proof-
  have "\<lbrakk>mu (neg (negvar (neg (negvar f 0)) 0))\<rbrakk> M e = \<lbrakk>neg (nu (neg (negvar f 0)))\<rbrakk> M e" by (simp only: negnu)
  hence "\<lbrakk>neg (mu (neg (negvar (neg (negvar f 0)) 0)))\<rbrakk> M e = \<lbrakk>neg (neg (nu (neg (negvar f 0))))\<rbrakk> M e" by auto
  thus ?thesis by simp
qed

text \<open>Defining the occurrence and dependence of variables, together with some results on these functions.\<close>

fun occursvar :: "'a formula \<Rightarrow> nat \<Rightarrow> bool "
where 
  "occursvar tt i = False " |
  "occursvar ff i = False" |
  "occursvar (var X) i = (i = X)" |
  "occursvar (neg f) i = occursvar f i" |
  "occursvar (and' f f') i = ((occursvar f i) \<or> (occursvar f' i))" |
  "occursvar (or f f') i = ((occursvar f i) \<or> (occursvar f' i))" |
  "occursvar (diamond act f) i = occursvar f i " |
  "occursvar (box act f) i = occursvar f i" |
  "occursvar (nu f) i = occursvar f (Suc i)" |
  "occursvar (mu f) i = occursvar f (Suc i)"

lemma shiftdown_shiftdownenv [simp] : "\<not>occursvar f i \<longrightarrow> \<lbrakk>shiftdown f i\<rbrakk> M (shiftdownenv e i) = \<lbrakk>f\<rbrakk> M e"
  apply (induct f arbitrary: e i; simp add: shiftdownenv_def; (arith|rule impI); subst switchnewenvironmentshiftdown)
proof-
  fix f e i
  assume assum1 : "(\<And>e i. \<not>occursvar f i \<longrightarrow> (\<lbrakk>shiftdown f i\<rbrakk> M (shiftdownenv e i)) = (\<lbrakk>f\<rbrakk> M e))"
  assume assum2 : "\<not>occursvar f (Suc i)"
  hence "\<forall>S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) = \<lbrakk>f\<rbrakk> M (newenvironment e S')" using assum1 by blast
  thus "\<Inter> {S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S'}" by auto
next
  fix f e i
  assume assum1 : "(\<And>e i. \<not>occursvar f i \<longrightarrow> (\<lbrakk>shiftdown f i\<rbrakk> M (shiftdownenv e i)) = (\<lbrakk>f\<rbrakk> M e))"
  assume assum2 : "\<not>occursvar f (Suc i)"
  hence "\<forall>S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) = \<lbrakk>f\<rbrakk> M (newenvironment e S')" using assum1 by blast
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by auto
qed

lemma closedformula : "(\<forall>i \<ge> j. \<not>occursvar f i) \<and> (\<forall>i < j. e i = e' i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
  apply (induct f arbitrary: e e' j; simp)
  using linorder_le_less_linear apply blast
  apply blast
  apply blast
  apply (subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')")
  apply simp
  prefer 2 
  apply (subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')")
  apply simp
proof-
  fix f j S'
  fix e e' :: "nat \<Rightarrow> 'b set"
  assume "(\<And>e e' j. (\<forall>i\<ge>j. \<not>occursvar f i) \<and> (\<forall>i<j. e i = e' i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e')"
  moreover {
    assume "\<forall>i\<ge>j. \<not>occursvar f (Suc i)"
    hence "\<forall>i \<ge> Suc j. \<not>occursvar f i" using Suc_le_D by auto 
  }
  moreover {
    assume assum1 : "\<forall>i<j. e i = e' i"
    have "\<forall>i<Suc j. newenvironment e S' i = newenvironment e' S' i" 
      by (rule; induct_tac i; simp add: assum1)
  }
  moreover assume "(\<forall>i\<ge>j. \<not> occursvar f (Suc i)) \<and> (\<forall>i<j. e i = e' i)"
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')" by auto
  thus "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')" by simp
qed

lemma closedformulacoro : "(\<And>i. \<not>occursvar f i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
  using closedformula less_nat_zero_code by metis

lemma shiftupnotoccurs [simp] : "\<not>occursvar (shiftup f i) i"
  by (induct f arbitrary : i; simp)

lemma shiftuplemma [simp] : "\<lbrakk>shiftup f 0\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M e"
proof-
  have "\<lbrakk>shiftdown (shiftup f 0) 0\<rbrakk> M (shiftdownenv (newenvironment e S') 0) = \<lbrakk>shiftup f 0\<rbrakk> M (newenvironment e S')" using shiftupnotoccurs shiftdown_shiftdownenv by metis
  thus "\<lbrakk>shiftup f 0\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M e" using shiftupanddown shiftdownnewenvzero_eq_newenv by metis
qed

lemma DiamondPlus : 
  assumes "\<And>f g. \<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R\<rangle>\<^sub>R g\<rbrakk> M e"
  and "\<And>f g. \<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>\<langle>Q\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>Q\<rangle>\<^sub>R g\<rbrakk> M e"
  and "\<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e" 
  shows "\<lbrakk>\<langle>R +\<^sub>R Q\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R +\<^sub>R Q\<rangle>\<^sub>R g\<rbrakk> M e"
proof-
  have "\<lbrakk>Diamond R f\<rbrakk> M e = \<lbrakk>Diamond R g\<rbrakk> M e \<and> \<lbrakk>Diamond Q f\<rbrakk> M e = \<lbrakk>Diamond Q g\<rbrakk> M e" using assms by blast
  thus "\<lbrakk>Diamond (Plus R Q) f\<rbrakk> M e = \<lbrakk>Diamond (Plus R Q) g\<rbrakk> M e" by simp
qed

lemma DiamondTimes : 
  assumes "\<And>f g. \<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R\<rangle>\<^sub>R g\<rbrakk> M e"
  and "\<And>f g. \<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>\<langle>Q\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>Q\<rangle>\<^sub>R g\<rbrakk> M e"
  and "\<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e" 
  shows "\<lbrakk>\<langle>R \<cdot> Q\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R \<cdot> Q\<rangle>\<^sub>R g\<rbrakk> M e"
proof-
  have "\<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e = \<lbrakk>Diamond R (Diamond Q g)\<rbrakk> M e" using assms by blast
  thus "\<lbrakk>Diamond (Times R Q) f\<rbrakk> M e = \<lbrakk>Diamond (Times R Q) g\<rbrakk> M e" by simp
qed

lemma Diamond_eq : "\<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R\<rangle>\<^sub>R g\<rbrakk> M e"
  by (induct R arbitrary: f g; (((rule DiamondPlus|rule DiamondTimes); blast)|simp))

lemma occursvarshiftup : "m \<le> i \<Longrightarrow> occursvar (shiftup f m) (Suc i) = occursvar f i"
  by (induct f arbitrary : i m; simp)

lemma occursDiamond [simp] : "(occursvar (\<langle>R\<rangle>\<^sub>R f) i) = (occursvar f i \<and> \<not>rexp_empty R)"
  by (induct R arbitrary : f i; simp add : occursvarshiftup; auto)

lemma occursBox [simp] : "(occursvar ([R]\<^sub>R f) i) = (occursvar f i \<and> \<not>rexp_empty R)"
  by (induct R arbitrary : f i; simp add : occursvarshiftup; auto)

lemma negBox : "\<lbrakk>\<not>\<^sub>\<mu>[R]\<^sub>R f\<rbrakk> M e = \<lbrakk>\<langle>R\<rangle>\<^sub>R (\<not>\<^sub>\<mu>f)\<rbrakk> M e"
  apply (induct R arbitrary: f e; simp)
  apply blast
proof-
  fix R Q f e
  assume "\<And>f e. -(\<lbrakk>Box Q f\<rbrakk> M e) =  \<lbrakk>Diamond Q (neg f)\<rbrakk> M e"
  hence "\<lbrakk>neg (Box Q f)\<rbrakk> M e = \<lbrakk>Diamond Q (neg f)\<rbrakk> M e" by simp
  thus "\<lbrakk>Diamond R (neg (Box Q f))\<rbrakk> M e = \<lbrakk>Diamond R (Diamond Q (neg f))\<rbrakk> M e" using Diamond_eq by blast
next
  fix R f e
  assume "\<And>f e. -(\<lbrakk>Box R f\<rbrakk> M e) = \<lbrakk>Diamond R (neg f)\<rbrakk> M e" 
  hence "\<And>S'. -(\<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e (-S'))) = \<lbrakk>Diamond R (neg (var 0))\<rbrakk> M (newenvironment e (-S'))" by blast
  moreover have "\<And>S'. \<lbrakk>Diamond R (neg (var 0))\<rbrakk> M (newenvironment e (-S')) = \<lbrakk>negvar (Diamond R (neg (var 0))) 0\<rbrakk> M (newenvironment e S')" using movenegvarin newenvironmentzerocomplement by metis
  ultimately have "\<And>S'. -(\<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e (-S'))) = \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S')" by (simp add: Diamond_eq)
  moreover have "- \<Union> {S'. S' \<subseteq> \<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e S') \<and> S' \<subseteq> \<lbrakk>f\<rbrakk> M e} = \<Inter> {S'. -S' \<subseteq> \<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e (-S')) \<and> -S' \<subseteq> \<lbrakk>f\<rbrakk> M e}" by (rule negcupcap)
  moreover have "... =  \<Inter> {S'. -(\<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e (-S'))) \<subseteq> S' \<and> -(\<lbrakk>f\<rbrakk> M e) \<subseteq> S'}" using compl_le_swap2 by meson
  ultimately show "- \<Union> {S'. S' \<subseteq> \<lbrakk>Box R (var 0)\<rbrakk> M (newenvironment e S') \<and> S' \<subseteq> \<lbrakk>f\<rbrakk> M e} = \<Inter> {S'. \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S') \<subseteq> S' \<and> -(\<lbrakk>f\<rbrakk> M e) \<subseteq> S'}" by auto
qed

lemma negDiamond : "\<lbrakk>\<not>\<^sub>\<mu>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = \<lbrakk>[R]\<^sub>R (\<not>\<^sub>\<mu>f)\<rbrakk> M e"
proof-
  have "\<lbrakk>Diamond R f\<rbrakk> M e = \<lbrakk>neg (Box R (neg f))\<rbrakk> M e" using Diamond_eq negBox negnegf by metis
  thus ?thesis by simp
qed

lemma Box_eq : "\<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e \<Longrightarrow> \<lbrakk>[R]\<^sub>R f\<rbrakk> M e = \<lbrakk>[R]\<^sub>R g\<rbrakk> M e"
proof-
  assume "\<lbrakk>f\<rbrakk> M e = \<lbrakk>g\<rbrakk> M e"
  hence "\<lbrakk>neg f\<rbrakk> M e = \<lbrakk>neg g\<rbrakk> M e" by simp
  hence "\<lbrakk>Diamond R (neg f)\<rbrakk> M e = \<lbrakk>Diamond R (neg g)\<rbrakk> M e" by (rule Diamond_eq)
  hence "\<lbrakk>neg (Box R f)\<rbrakk> M e = \<lbrakk>neg (Box R g)\<rbrakk> M e" by (simp only: negBox)
  thus "\<lbrakk>Box R f\<rbrakk> M e = \<lbrakk>Box R g\<rbrakk> M e" by simp
qed

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = \<lbrakk>f\<rbrakk> M (newenvironment e S')"

lemma transformerdef : "transformer f M e = (\<lambda>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S'))"
  by (rule; simp add: transformer_def)

definition dependvar :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> nat \<Rightarrow> bool" where
"dependvar f M i = (\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M (e(i := S')))"

lemma notdependshiftdown : "\<not>dependvar f M 0 \<Longrightarrow> \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>shiftdown f 0\<rbrakk> M e"
proof- 
  assume "\<not>dependvar f M 0"
  hence "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>f\<rbrakk> M (newenvironment e (e 0))(0 := S')" using dependvar_def by metis
  moreover have "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>shiftdown f 0\<rbrakk> M e" using shiftdownnewenv by metis
  moreover have "(newenvironment e (e 0))(0 := S') = newenvironment e S'" by simp
  ultimately show ?thesis by (simp add: shiftdownenvrepeat)
qed

lemma dependvarX : "dependvar (var X) M i = (X = i)"
  by (auto simp: dependvar_def)

lemma dependvarneg : "dependvar (neg f) M i = dependvar f M i"
  by (simp add: dependvar_def)

lemma dependvarandor : "\<not>dependvar f1 M i \<and> \<not>dependvar f2 M i \<Longrightarrow> \<not>dependvar (and' f1 f2) M i \<and> \<not>dependvar (or f1 f2) M i"
  by (simp add: dependvar_def)

lemma dependvarboxdiamond : "\<not>dependvar f M i  \<Longrightarrow> \<not>dependvar (box a f) M i \<and> \<not>dependvar (diamond a f) M i"
  by (simp add: dependvar_def)

lemma dependvarnumu : "\<not>dependvar f M (Suc i)  \<Longrightarrow> \<not>dependvar (nu f) M i \<and> \<not>dependvar (mu f) M i"
  by (simp add: dependvar_def)

lemma shiftup_envrepeati [simp] : "\<lbrakk>shiftup f m\<rbrakk> M (envrepeati e m) = \<lbrakk>f\<rbrakk> M e"
  using shiftdownenvrepeat shiftupanddown by metis

lemma notoccursnotdepends : "\<not>occursvar f i \<Longrightarrow> \<not>dependvar f M i"
  apply (induct f arbitrary: i; simp add: dependvarneg dependvarandor dependvarboxdiamond dependvarnumu)
  apply (simp_all add: dependvar_def)
  done

lemma dependsoccurs : "dependvar f M i \<Longrightarrow> occursvar f i"
  using notoccursnotdepends by auto

lemma dependvarshiftup [simp] : "m \<le> i \<Longrightarrow> dependvar (shiftup f m) M (Suc i) = dependvar f M i" 
  apply (simp add: dependvar_def)
proof
  assume "\<exists>e S'. \<lbrakk>shiftup f m\<rbrakk> M e \<noteq> \<lbrakk>shiftup f m\<rbrakk> M e(Suc i := S')"
  then obtain e S' where "\<lbrakk>shiftup f m\<rbrakk> M e \<noteq> \<lbrakk>shiftup f m\<rbrakk> M e(Suc i := S')" by auto
  hence "\<lbrakk>shiftdown (shiftup f m) m\<rbrakk> M (shiftdownenv e m) \<noteq> \<lbrakk>shiftdown (shiftup f m) m\<rbrakk> M (shiftdownenv (e(Suc i := S')) m)" by simp
  moreover assume "m \<le> i"
  moreover have "m \<le> i \<Longrightarrow> (shiftdownenv (e(Suc i := S')) m) = (shiftdownenv e m)(i := S')" by (rule; simp add: shiftdownenv_def)
  ultimately have "\<lbrakk>f\<rbrakk> M (shiftdownenv e m) \<noteq> \<lbrakk>f\<rbrakk> M (shiftdownenv e m)(i := S')" by (simp add: shiftupanddown)
  thus "\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M e(i := S')" by auto
next
  assume "\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M e(i := S')"
  then obtain e S' where "\<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M e(i := S')" by auto
  moreover have "\<not>dependvar (shiftup f m) M m" using shiftupnotoccurs notoccursnotdepends by blast
  ultimately have "\<lbrakk>shiftup f m\<rbrakk> M (envrepeati e m) \<noteq> \<lbrakk>shiftup f m\<rbrakk> M (envrepeati (e(i := S')) m) (m := e m)" by (simp add: dependvar_def)
  moreover assume "m \<le> i"
  moreover have "m \<le> i \<Longrightarrow>((envrepeati (e(i := S')) m) (m := e m)) = (envrepeati e m) (Suc i := S')" by (rule; simp add: envrepeatidef; arith)
  ultimately have "\<lbrakk>shiftup f m\<rbrakk> M (envrepeati e m) \<noteq> \<lbrakk>shiftup f m\<rbrakk> M (envrepeati e m)(Suc i := S')" by simp
  thus "\<exists>e S'. \<lbrakk>shiftup f m\<rbrakk> M e \<noteq> \<lbrakk>shiftup f m\<rbrakk> M e(Suc i := S')" by auto
qed

lemma dependvarBoxDiamond : "\<not>dependvar f M i  \<Longrightarrow> \<not>dependvar (Box R f) M i \<and> \<not>dependvar (Diamond R f) M i"
  by (induct R arbitrary: f i; simp add: dependvarX dependvarandor dependvarnumu; simp add: dependvar_def)

lemma concsubst : "length e = Suc i \<Longrightarrow> (conc (take i e) (S' ## env)) (i := e!i) = conc e env"
proof
  fix j
  assume assum1: "length e = Suc i"
  have "j < i \<or> j = i \<or> j \<ge> Suc i" by auto
  moreover {
    assume "j < i"
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  moreover {
    assume "j = i"
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  moreover {
    assume "j \<ge> Suc i"
    hence "j - i = Suc (j - Suc i)" by auto
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  ultimately show "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" by auto
qed

lemma notdependfirstpart : "(\<forall>i < j. \<not>dependvar f M i) \<and> (length e = length e' \<and> length e \<le> j)
    \<Longrightarrow> \<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)"
  apply (induct j arbitrary: e e' env)
  apply auto[1]
proof-
  fix j env
  fix e e' :: "'b set list"
  assume assum1 : "(\<And>e e' env. (\<forall>i<j. \<not> dependvar f M i) \<and> length e = length e' \<and> length e \<le> j \<Longrightarrow> \<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env))"
  assume assum2 : "(\<forall>i<Suc j. \<not> dependvar f M i) \<and> length e = length e' \<and> length e \<le> Suc j"
  hence " length e = Suc j \<or> length e \<le> j" by auto
  moreover {
    have "\<lbrakk>f\<rbrakk> M (conc (take j e) (env 0 ## env)) = \<lbrakk>f\<rbrakk> M (conc (take j e') (env 0 ## env))" by (simp add: assum1 assum2)
    hence "\<lbrakk>f\<rbrakk> M ((conc (take j e) (env 0 ## env)) (j := e!j)) = \<lbrakk>f\<rbrakk> M ((conc (take j e') (env 0 ## env)) (j := e'!j))" using assum2 by (simp add: dependvar_def)
    moreover assume "length e = Suc j"
    ultimately have "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" using concsubst assum2 by metis 
  }
  moreover {
    assume "length e \<le> j"
    moreover have "(\<forall>i<j. \<not> dependvar f M i) \<and> length e = length e'" using assum2 by auto
    ultimately have "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" using assum1 by metis
  }
  ultimately show "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" by auto
qed

lemma existsmaxoccurs : "\<exists>j. \<forall>i \<ge> j. \<not>occursvar f i"
  apply (induct f; simp)
  using Suc_n_not_le_n apply blast
  using le_trans nat_le_linear apply metis
  using le_trans nat_le_linear apply metis
  using le_Suc_eq apply auto
  done

lemma notdependlastpart : "(\<forall>i\<ge>length elist. \<not>occursvar f i) \<longrightarrow> \<lbrakk>f\<rbrakk> M (conc elist e) = \<lbrakk>f\<rbrakk> M (conc elist e')"
  apply (induct f arbitrary : e e' elist; simp; rule impI)
  apply (subgoal_tac "x < length elist")
  apply simp
  apply arith
  apply blast
  apply blast
  apply blast
  apply blast
proof-
  fix f e e' 
  fix elist :: "'a set list"
  assume assum1: "(\<And>e e' elist. (\<forall>i\<ge>length elist. \<not> occursvar f i) \<longrightarrow> \<lbrakk>f\<rbrakk> M (elist \<frown> e) = \<lbrakk>f\<rbrakk> M (elist \<frown> e'))"
  assume "\<forall>i\<ge>length elist. \<not> occursvar f (Suc i)"
  hence "\<forall>i \<ge> Suc (length elist). \<not> occursvar f i" using Suc_le_D by auto
  moreover have "\<And>S'. length (S' # elist) = Suc (length elist)" by simp
  ultimately have conclusion : "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S') = \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S')" using assum1 build_cons by metis
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S')} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S')}" by auto
  thus "\<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S') \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S') \<subseteq> S'}" using conclusion by auto
qed

text \<open>If a formula does not depend on any variable, we can change its environment without changing
its semantics.\<close>

lemma notdependchangeenv : "(\<And>i. \<not>dependvar f M i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
proof-
  obtain j where assum1:"\<forall>i \<ge> j. \<not>occursvar f i" using existsmaxoccurs by auto
  assume "\<And>i. \<not>dependvar f M i"
  hence "\<forall>i<j. \<not>dependvar f M i" by auto
  moreover have "length (prefix j e) = length (prefix j e') \<and> length (prefix j e) \<le> j" by auto
  ultimately have res1: "\<lbrakk>f\<rbrakk> M (conc (prefix j e) (suffix j e)) = \<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e))" using notdependfirstpart by metis
  have "length (prefix j e') = j" by auto
  hence res2: "\<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e)) = \<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e'))" using assum1 notdependlastpart by metis
  show ?thesis using res1 res2 by auto
qed

lemma notdependseqnu :
  assumes "\<not>dependvar f M 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>nu f\<rbrakk> M e"
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms dependvar_def by blast
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  hence "\<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S'')} = \<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by blast
  thus ?thesis by auto
qed

lemma notdependseqmu :
  assumes "\<not>dependvar f M 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>mu f\<rbrakk> M e"
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms dependvar_def by blast
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  hence "\<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') \<subseteq> S''} = \<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S''}" by blast
  thus ?thesis by auto
qed

lemma notdependsmono : "\<not>dependvar f M i \<Longrightarrow>
  mono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S)))) \<and> antimono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S))))"
  by (induct f arbitrary: i; simp add: dependvar_def monotone_def)

lemma notdependscoro : "(\<not>dependvar f M 0 \<longrightarrow> mono (transformer f M e))"
proof-
  have "\<forall>S''. \<not>dependvar f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using notdependsmono by metis
  hence "\<not>dependvar f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
  thus ?thesis by (simp add: transformerdef)
qed

lemma andsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<and> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>1 \<and> A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>2"
  using assms by auto

lemma orsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<or> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<or> A\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
  using assms by auto

text \<open>Defining function \<open>notdependalloccursposneg\<close> that can be evaluated on formulas and
proving that this evaluation can imply monotonicity (or antimonotonicity).\<close>

fun notdependalloccursposneg :: "'a formula \<Rightarrow> ('a ,'s) lts \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "notdependalloccursposneg tt M i b = True " |
  "notdependalloccursposneg ff M i b = True" |
  "notdependalloccursposneg (var X) M i b = ((X \<noteq> i) \<or> b)" |
  "notdependalloccursposneg (neg f) M i b = (\<not>dependvar f M i \<or> notdependalloccursposneg f M i (\<not>b))" |
  "notdependalloccursposneg (and' f f') M i b = (\<not>dependvar (and' f f') M i \<or> (notdependalloccursposneg f M i b \<and> notdependalloccursposneg f' M i b))" |
  "notdependalloccursposneg (or f f') M i b = (\<not>dependvar (or f f') M i \<or> (notdependalloccursposneg f M i b \<and> notdependalloccursposneg f' M i b))" |
  "notdependalloccursposneg (box act f) M i b = (\<not>dependvar (box act f) M i \<or> notdependalloccursposneg f M i b)" |
  "notdependalloccursposneg (diamond act f) M i b = (\<not>dependvar (diamond act f) M i \<or> notdependalloccursposneg f M i b) " |  
  "notdependalloccursposneg (nu f) M i b = (\<not>dependvar (nu f) M i \<or> notdependalloccursposneg f M (Suc i) b)" |
  "notdependalloccursposneg (mu f) M i b = (\<not>dependvar (mu f) M i \<or> notdependalloccursposneg f M (Suc i) b)"

lemma notdepends : "\<not>dependvar f M i \<Longrightarrow> notdependalloccursposneg f M i b"
  apply (induct f arbitrary : i b; simp add: dependvar_def)
  apply (rule impI)
  apply auto
  done

lemma notdependalloccursposneg_shiftup : "m \<le> i \<Longrightarrow> notdependalloccursposneg (shiftup f m) M (Suc i) b = notdependalloccursposneg f M i b"
  apply (induct f arbitrary: b m i; simp)
  apply (metis dependvarshiftup shiftup.simps(5))
  apply (metis dependvarshiftup shiftup.simps(6))
  apply (metis dependvarshiftup shiftup.simps(7))
  apply (metis dependvarshiftup shiftup.simps(8))
  apply (metis dependvarshiftup shiftup.simps(9))
  apply (metis dependvarshiftup shiftup.simps(10))
  done

lemma notdependalloccursposneg_Diamond [simp] : "notdependalloccursposneg (\<langle>R\<rangle>\<^sub>R f) M i b = (\<not>dependvar (\<langle>R\<rangle>\<^sub>R f) M i \<or> notdependalloccursposneg f M i b)"
  apply (induct R arbitrary: f i b)
  apply (simp add: dependvar_def)
  using notdepends apply auto[1]
  apply (simp add: dependvar_def)
  using dependvarandor apply fastforce
  apply simp
  using dependvarBoxDiamond apply fastforce
proof-
  case IH: (Star R) 
  have "notdependalloccursposneg (Diamond (Star R) f) M i b = (\<not> dependvar (Diamond (Star R) f) M i \<or> \<not> dependvar (or (Diamond R (var 0)) (shiftup f 0)) M (Suc i) \<or> (notdependalloccursposneg (Diamond R (var 0)) M (Suc i) b \<and> notdependalloccursposneg (shiftup f 0) M (Suc i) b))" by simp
  hence "notdependalloccursposneg (Diamond (Star R) f) M i b = (\<not> dependvar (Diamond (Star R) f) M i \<or> \<not> dependvar (shiftup f 0) M (Suc i) \<or> notdependalloccursposneg (shiftup f 0) M (Suc i) b)"
    using  Diamond.simps(6) dependvarX IH dependvarnumu nat.distinct(1) notdepends by metis
  moreover have "notdependalloccursposneg (shiftup f 0) M (Suc i) b = notdependalloccursposneg f M i b" using notdependalloccursposneg_shiftup by blast
  ultimately show ?case using notdepends by auto
qed

lemma notdependalloccursposneg_Box [simp] : "notdependalloccursposneg ([R]\<^sub>R f) M i b = (\<not>dependvar ([R]\<^sub>R f) M i \<or> notdependalloccursposneg f M i b)"
  apply (induct R arbitrary: f i b)
  apply (simp add: dependvar_def)
  using notdepends apply auto[1]
  apply (simp add: dependvar_def)
  using dependvarandor apply fastforce
  apply simp
  using dependvarBoxDiamond apply fastforce
proof-
  case IH : (Star R)
  have "notdependalloccursposneg (Box (Star R) f) M i b = (\<not> dependvar (Box (Star R) f) M i \<or> \<not> dependvar (and' (Box R (var 0)) (shiftup f 0)) M (Suc i) \<or> (notdependalloccursposneg (Box R (var 0)) M (Suc i) b \<and> notdependalloccursposneg (shiftup f 0) M (Suc i) b))" by simp
  hence "notdependalloccursposneg (Box (Star R) f) M i b = (\<not> dependvar (Box (Star R) f) M i \<or> \<not> dependvar (shiftup f 0) M (Suc i) \<or> notdependalloccursposneg (shiftup f 0) M (Suc i) b)"
    using Box.simps(6) IH dependvarX dependvarnumu nat.distinct(1) notdepends by metis
  moreover have "notdependalloccursposneg (shiftup f 0) M (Suc i) b = notdependalloccursposneg f M i b" using notdependalloccursposneg_shiftup by blast
  ultimately show ?case using notdepends by auto
qed

lemma andormonoantimono : 
  shows "mono f1 \<and> mono f2 \<Longrightarrow> mono (\<lambda>S'. f1 S' \<inter> f2 S') \<and>  mono (\<lambda>S'. f1 S' \<union> f2 S')"
  and "antimono f1 \<and> antimono f2 \<Longrightarrow> antimono (\<lambda>S'. f1 S' \<inter> f2 S') \<and> antimono (\<lambda>S'. f1 S' \<union> f2 S')"
  apply (simp_all add: monotone_def andsubset orsubset)
  apply blast+
  done

lemma boxdiamondmonoantimono : 
  shows "mono f \<Longrightarrow> mono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'}) \<and> mono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  and "antimono f \<Longrightarrow> antimono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'}) \<and> antimono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  apply (simp_all add: monotone_def)
  using monoD apply blast+
  done

lemma numumono : 
  assumes "\<And>S''. mono (f S'')"
  shows "mono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "mono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI impI)+
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' x \<longrightarrow> S'' \<subseteq> f S'' y")
  apply (simp add: Collect_mono_iff Sup_subset_mono)
  using assms monotoneD apply fastforce
  apply (rule allI impI)+
  apply (subgoal_tac "\<forall>S''. f S'' y \<subseteq> S'' \<longrightarrow> f S'' x \<subseteq> S''")
  apply (simp add: Collect_mono_iff Inf_superset_mono)
  using assms monotoneD apply fastforce
  done

lemma numuantimono : 
  assumes "\<And>S''. antimono (f S'')"
  shows "antimono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "antimono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI impI)+
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' y \<longrightarrow> S'' \<subseteq> f S'' x")
  apply (simp add: Collect_mono_iff Sup_subset_mono)
  using assms monotoneD apply fastforce
  apply (rule allI impI)+
  apply (subgoal_tac "\<forall>S''. f S'' x \<subseteq> S'' \<longrightarrow> f S'' y \<subseteq> S''")
  apply (simp add: Collect_mono_iff Inf_superset_mono)
  using assms monotoneD apply fastforce
  done

lemma monotonicitynotdepend :
"(notdependalloccursposneg f M i True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))
 \<and> (notdependalloccursposneg f M i False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))"
  apply (induct f arbitrary : i e; simp only: notdependalloccursposneg.simps)
  apply (simp add: monotone_def)+
  apply (metis notdepends)
proof-
  fix f1 f2 i e
  assume assum1: "(\<And>i e. (notdependalloccursposneg f1 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposneg f1 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))))"
  assume assum2: "(\<And>i e. (notdependalloccursposneg f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposneg f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))))"
  have "\<not> dependvar (and' f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f1 M i True \<and> notdependalloccursposneg f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormonoantimono)
  moreover have "notdependalloccursposneg f1 M i False \<and> notdependalloccursposneg f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormonoantimono)
  ultimately show "(\<not> dependvar (and' f1 f2) M i \<or> notdependalloccursposneg f1 M i True \<and> notdependalloccursposneg f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (and' f1 f2) M i \<or> notdependalloccursposneg f1 M i False \<and> notdependalloccursposneg f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvar (or f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f1 M i True \<and> notdependalloccursposneg f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormonoantimono)
  moreover have "notdependalloccursposneg f1 M i False \<and> notdependalloccursposneg f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormonoantimono)
  ultimately show "(\<not> dependvar (or f1 f2) M i \<or> notdependalloccursposneg f1 M i True \<and> notdependalloccursposneg f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (or f1 f2) M i \<or> notdependalloccursposneg f1 M i False \<and> notdependalloccursposneg f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" by auto
next
  fix a f i e
  assume assum1: "(\<And>i e. (notdependalloccursposneg f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposneg f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvar (box a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmonoantimono)
  moreover have "notdependalloccursposneg f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmonoantimono)
  ultimately show "(\<not> dependvar (box a f) M i \<or> notdependalloccursposneg f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (box a f) M i \<or> notdependalloccursposneg f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvar (diamond a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmonoantimono)
  moreover have "notdependalloccursposneg f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmonoantimono)
  ultimately show "(\<not> dependvar (diamond a f) M i \<or> notdependalloccursposneg f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (diamond a f) M i \<or> notdependalloccursposneg f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" by auto
next
  fix f i e
  assume assum1: "(\<And>i e. (notdependalloccursposneg f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposneg f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvar (nu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposneg f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvar (nu f) M i \<or> notdependalloccursposneg f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (nu f) M i \<or> notdependalloccursposneg f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvar (mu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposneg f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposneg f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvar (mu f) M i \<or> notdependalloccursposneg f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvar (mu f) M i \<or> notdependalloccursposneg f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" by auto
qed

text \<open>\<open>notdependalloccursposneg\<close> can be evaluated on formulas so that the following lemma can be used
to prove that its transformer is monotone.\<close>

lemma monotonicitynotdependcoro : 
  shows "notdependalloccursposneg f M 0 True \<Longrightarrow> mono (transformer f M e)"
  and "notdependalloccursposneg f M 0 False \<Longrightarrow> antimono (transformer f M e)"
  apply (simp_all add: transformerdef)
proof-
  have "\<forall>S''. notdependalloccursposneg f M 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposneg f M 0 True \<Longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
next
  have "\<forall>S''. notdependalloccursposneg f M 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposneg f M 0 False \<Longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

subsection \<open>Approximation of \<open>nu\<close> and \<open>mu\<close>.\<close>

lemma gfp_eq_nu [simp] :
"gfp (transformer f M e) = \<lbrakk>\<nu> f\<rbrakk> M e"
  by (simp add: gfp_def transformer_def)

lemma lfp_eq_mu [simp] :
"lfp (transformer f M e) = \<lbrakk>\<mu> f\<rbrakk> M e"
  by (simp add: lfp_def transformer_def)

lemma monosubset :
  assumes "mono f"
  shows "(f S' \<subseteq> S' \<longrightarrow> (f^^(Suc i)) S' \<subseteq> (f^^i) S') \<and>
    (S' \<subseteq> f S' \<longrightarrow> (f^^ i) S' \<subseteq> (f^^(Suc i)) S')"
  using assms by (induct i; simp add: mono_def)

lemma fpoweriplusn : 
  assumes "((f :: 'a \<Rightarrow> 'a)^^i) S' = (f^^(Suc i)) S'"
  shows "(f^^(i + n)) S' = (f^^(Suc i + n)) S'" 
  apply (induct n)
  using assms apply simp
proof-
  case (Suc n)
  hence "(f ^^ (i + n)) S' = (f ^^ (Suc i + n)) S'" by blast
  hence "f ((f ^^ (i + n)) S') = f ((f ^^ Suc (i + n)) S')" by simp
  thus ?case by simp
qed

lemma fixpointmono:
  assumes "mono (f :: ('s set \<Rightarrow> 's set))"
  and "finite (UNIV :: 's set)"
  and "S' \<subseteq> f S' \<or> f S' \<subseteq> S'"
  shows "\<exists>n \<le> card(UNIV :: 's set). (f^^n) S' = (f^^(Suc n)) S'"
proof (rule ccontr)
  assume "\<not> (\<exists>n\<le>card(UNIV :: 's set).((f ^^ n) S') = ((f ^^ Suc n) S'))"
  hence assum1 : "\<forall>n\<le>card(UNIV :: 's set).((f ^^ n) S') \<noteq> ((f ^^ Suc n) S')" by auto
  {
    assume assum2 : "S' \<subseteq> f S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((f ^^ n) S') \<ge> n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        apply (induct n)
        apply simp
      proof
        fix n
        assume IH: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        assume assum3 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ n) S' \<subseteq> (f ^^ (Suc n)) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ n) S' \<subset> (f ^^ (Suc n)) S'" by simp
        moreover have "finite ((f ^^ Suc n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ n) S') < card ((f ^^ Suc n) S')" using psubset_card_mono by metis
        thus "Suc n \<le> card ((f ^^ Suc n) S')" using assum3 IH by simp
      qed
    qed
    hence contradiction1 : "card ((f ^^ Suc (card(UNIV :: 's set))) S') \<ge>  Suc (card(UNIV :: 's set))" by auto
    have contradiction2: "card ((f ^^ Suc (card(UNIV :: 's set))) S') \<le> card(UNIV :: 's set)" using assms(2) card_mono by auto
    have False using contradiction1 contradiction2 by auto
  }
  moreover{
    assume assum2 : "f S' \<subseteq> S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((f ^^ n) S') < Suc(card(UNIV :: 's set)) - n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> card ((f ^^ n) S') < Suc (card(UNIV :: 's set)) - n"
        apply (induct n)
        apply (simp add : assms(2) card_mono less_Suc_eq_le)
      proof
        fix n
        assume IH: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> card ((f ^^ n) S') < Suc(card (UNIV :: 's set)) - n"
        assume assum3 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ (Suc n)) S' \<subseteq> (f ^^ n) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ (Suc n)) S' \<subset> (f ^^  n) S'" using psubset_eq by simp
        moreover have "finite ((f ^^ n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ (Suc n)) S') < card ((f ^^ n) S')" using psubset_card_mono by metis
        thus "card ((f ^^ Suc n) S') < Suc(card (UNIV :: 's set)) - (Suc n)" using assum3 IH by simp
      qed
    qed
    hence "card ((f ^^ Suc (card(UNIV :: 's set))) UNIV) <  0" by auto
    hence False by auto
  }
  ultimately show False using assms(3) by auto
qed

lemma gfp_monofin [simp] :
  assumes "finite (UNIV :: 's set)"
  and "mono (f :: 's set \<Rightarrow> 's set)"
  shows "(f^^(card (UNIV :: 's set))) UNIV = gfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" using assms fixpointmono by blast
  then obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" by auto
  hence "(f ^^ (n + (card (UNIV :: 's set) - n))) (UNIV) = (f ^^ (Suc n +  (card (UNIV :: 's set) - n))) (UNIV)" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 's set)))(UNIV) = (f^^Suc(card (UNIV :: 's set)))(UNIV)" using assum2 by auto
  thus ?thesis using gfp_Kleene_iter assms(2) by blast
qed

lemma lfp_monofin [simp] :
  assumes "finite (UNIV :: 's set)"
  and "mono (f :: 's set \<Rightarrow> 's set)"
  shows "(f^^(card (UNIV :: 's set))) {} = lfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). (f^^n) {} = (f^^(Suc n)) {}" using assms fixpointmono by blast
  then obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  (f^^n) {} = (f^^(Suc n)) {}" by auto
  hence "(f ^^ (n + (card (UNIV :: 's set) - n))) {} = (f ^^ (Suc n +  (card (UNIV :: 's set) - n))) {}" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 's set))){} = (f^^Suc(card (UNIV :: 's set))){}" using assum2 by auto
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma transformer_eq_nu :
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f M e)"
  shows "\<lbrakk>\<nu> f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set)))(UNIV)"
  using assms by auto 

lemma transformer_eq_mu :
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f M e)"
  shows "\<lbrakk>\<mu> f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set))){}"
  using assms by auto

end