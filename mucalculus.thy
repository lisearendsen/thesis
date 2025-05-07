theory mucalculus
imports Main "HOL-Library.Omega_Words_Fun"
begin

section \<open>formulas\<close>

datatype 'a regularformula =
  eps | acts "'a list" |
  after "'a regularformula" "'a regularformula"| 
  union "'a regularformula" "'a regularformula" | 
  repeat "'a regularformula"

(* from "HOL-Library.Regular-Sets.Regular_Exp" *)
definition conc :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr \<open>@@\<close> 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

overloading form_pow == "compow :: nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
begin
  primrec form_pow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  "form_pow 0 A = {[]}" |
  "form_pow (Suc n) A = A @@ (form_pow n A)"
end

definition form_pow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  form_pow [code_abbrev]: "form_pow = compow"

fun regformtolanguage :: "'a regularformula \<Rightarrow> 'a list set" where
"regformtolanguage eps = {[]}" |
"regformtolanguage (acts []) = {}" |
"regformtolanguage (acts (a#as)) = {[a]} \<union> regformtolanguage (acts (as))" |
"regformtolanguage (after R Q) = ({r @ q |r q. (r \<in> regformtolanguage R) \<and> (q \<in> regformtolanguage Q)})" |
"regformtolanguage (union R Q) = (regformtolanguage R) \<union> (regformtolanguage Q)" |
"regformtolanguage (repeat R) = (\<Union>n. (regformtolanguage R) ^^ n)"

lemma regformtolanguage_acts : "regformtolanguage (acts A) = {[a] | a. a \<in> set A}"
  apply (induct A)
  apply (simp_all)
  apply (blast)
  done

value "regformtolanguage (eps) :: nat list set" 
value "regformtolanguage (after (acts [1, 2]) (acts [3, 4])) :: nat list set" 

datatype 'a formula =
  tt | ff | var nat |
  neg "'a formula" |
  and' "'a formula" "'a formula" | 
  or "'a formula" "'a formula" | 
  box 'a "'a formula" |
  diamond 'a "'a formula" |
  nu "'a formula" |
  mu "'a formula"

value "diamond 2 (box 1 tt) :: nat formula"
value "nu (var 0) :: nat formula "

record ('a, 's) lts =
transition :: "('s * 'a * 's) set"
initial :: "'s set"

fun newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S 0 = S" |
"newenvironment e S (Suc n) = e n"

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S)((Suc i) := - ((newenvironment e S) (Suc i))) = newenvironment (e(i := - e i)) S"
proof
  fix n
  show "((newenvironment e S) (Suc i := - newenvironment e S (Suc i))) n = newenvironment (e(i := - e i)) S n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S)(0 := (-(newenvironment e S) 0)) = (newenvironment e (-S))"
proof
  fix n
  show "((newenvironment e S)(0 := ((-(newenvironment e S) 0)))) n  = (newenvironment e (-S)) n "
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentswitchsuccessor [simp] : 
"(newenvironment e S'')((Suc i) := S') = newenvironment (e(i :=  S')) S''"
proof
  fix n
  show "((newenvironment e S'')((Suc i) := S')) n = (newenvironment (e(i :=  S')) S'') n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentswitchzero [simp] : 
"(newenvironment e S'')(0 := S') = newenvironment e S'"
proof
  fix n
  show "((newenvironment e S'')(0 := S')) n = newenvironment e S' n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentshift [simp] : 
"X > 0 \<longrightarrow> (newenvironment e S') X = e (X - Suc 0)"
  apply (induct_tac X)
  apply (simp_all)
  done

fun formulasemantics :: "'a formula  \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set" (\<open>\<lbrakk>_\<rbrakk> _ _\<close> [80, 80, 80] 80) 
where 
  "\<lbrakk>tt\<rbrakk> M e = UNIV " |
  "\<lbrakk>ff\<rbrakk> M e =  {}" |
  "\<lbrakk>var X\<rbrakk> M e  = e X" |
  "\<lbrakk>neg f\<rbrakk> M e = -(\<lbrakk>f\<rbrakk> M e)" |
  "\<lbrakk>and' f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<inter> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>or f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<union> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>diamond act f\<rbrakk> M e = {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and> s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>box act f\<rbrakk> M e = {s. \<forall> s'. (s, act, s') \<in> (transition M) \<longrightarrow>  s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>nu f\<rbrakk> M e = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" |
  "\<lbrakk>mu f\<rbrakk> M e = \<Inter> {S'. S' \<supseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}"

datatype 'a extendedformula =
  tt_e | ff_e | var_e nat |
  neg_e "'a extendedformula" |
  and'_e "'a extendedformula" "'a extendedformula"| 
  or_e "'a extendedformula" "'a extendedformula" | 
  box_e "'a regularformula" "'a extendedformula" |
  diamond_e "'a regularformula" "'a extendedformula" |
  nu_e "'a extendedformula" |
  mu_e "'a extendedformula"

fun shiftup :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftup tt i) = tt " |
  "(shiftup ff i) = ff" |
  "(shiftup (var X) i)  = (if X < i then var X else var (X + 1))" |
  "(shiftup (neg f) i) = neg (shiftup f i)" |
  "(shiftup (and' f f') i) = and' (shiftup f i) (shiftup f' i) " |
  "(shiftup (or f f') i) = or (shiftup f i) (shiftup f' i)" |
  "(shiftup (diamond act f) i) = diamond act (shiftup f i) " |
  "(shiftup (box act f) i) = box act (shiftup f i)" |
  "(shiftup (nu f) i) = nu (shiftup f (Suc i))" |
  "(shiftup (mu f) i) = mu (shiftup f (Suc i))"

fun extendedtoformula :: "'a extendedformula \<Rightarrow> 'a formula" where
"extendedtoformula tt_e = tt" |
"extendedtoformula ff_e = ff" |
"extendedtoformula (var_e X) = var X" |
"extendedtoformula (neg_e f) = neg (extendedtoformula f)" |
"extendedtoformula (and'_e f f') = and' (extendedtoformula f) (extendedtoformula f')" |
"extendedtoformula (or_e f f') = or (extendedtoformula f) (extendedtoformula f')" |
"extendedtoformula (box_e eps f) = (extendedtoformula f)" |
"extendedtoformula (box_e (acts []) f) = tt" |
"extendedtoformula (box_e (acts (a#as)) f) = and' (box a (extendedtoformula f)) (extendedtoformula (box_e (acts as) f))" |
"extendedtoformula (box_e (after R Q) f) = (extendedtoformula f) " (*should be (extendedtoformula (box_e R (box_e Q f)))*) |
"extendedtoformula (box_e (union R Q) f) = and' (extendedtoformula (box_e R f)) (extendedtoformula (box_e Q f))" |
"extendedtoformula (box_e (repeat R) f) = nu (and' (extendedtoformula (box_e R (var_e 0))) (shiftup (extendedtoformula f) 0))" |
"extendedtoformula (diamond_e eps f) = (extendedtoformula f)" |
"extendedtoformula (diamond_e (acts []) f) = ff" |
"extendedtoformula (diamond_e (acts (a#as)) f) = or (diamond a (extendedtoformula f)) (extendedtoformula (diamond_e (acts as) f))" |
"extendedtoformula (diamond_e (after R Q) f) = (extendedtoformula f)" (*should be (extendedtoformula (diamond_e R (diamond_e Q f)))*) |
"extendedtoformula (diamond_e (union R Q) f) = or (extendedtoformula (diamond_e R f)) (extendedtoformula (diamond_e Q f))" |
"extendedtoformula (diamond_e (repeat R) f) = mu (or (extendedtoformula (diamond_e R (var_e 0))) (shiftup (extendedtoformula f) 0))" |
"extendedtoformula (nu_e f) = nu (extendedtoformula f)" |
"extendedtoformula (mu_e f) = mu (extendedtoformula f)"

definition extendedformulasemantics :: "'a extendedformula  \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set"  (\<open>\<lbrakk>_\<rbrakk>\<^sub>e _ _\<close> [80, 80, 80] 80) 
where
"\<lbrakk>f\<rbrakk>\<^sub>e M e = \<lbrakk>extendedtoformula f\<rbrakk> M e"

lemma diamond_eq_exist : "(s \<in> \<lbrakk>diamond_e (acts A) f\<rbrakk>\<^sub>e M e) = (\<exists> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk>\<^sub>e M e)"
  apply (induct A)
  apply (simp_all add: extendedformulasemantics_def)
  apply (blast)
  done

lemma box_eq_forall : "(s \<in> \<lbrakk>box_e (acts A) f\<rbrakk>\<^sub>e M e) = (\<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk>\<^sub>e M e)"
  apply (induct A)
  apply (simp_all add: extendedformulasemantics_def)
  apply (blast)
  done

fun negvari :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(negvari tt i) = tt " |
  "(negvari ff i) = ff" |
  "(negvari (var X) i)  = (if i = X then (neg (var X)) else (var X))" |
  "(negvari (neg f) i) = neg (negvari f i)" |
  "(negvari (and' f f') i) = and' (negvari f i) (negvari f' i) " |
  "(negvari (or f f') i) = or (negvari f i) (negvari f' i)" |
  "(negvari (diamond act f) i) = diamond act (negvari f i) " |
  "(negvari (box act f) i) = box act (negvari f i)" |
  "(negvari (nu f) i) = nu (negvari f (Suc i))" |
  "(negvari (mu f) i) = mu (negvari f (Suc i))"

value "negvari (or (var 0) (mu (and' (var 0) (var 1)))) 0 :: nat formula"

fun occursvari :: "'a formula \<Rightarrow> nat \<Rightarrow> bool "
where 
  "(occursvari tt i) = False " |
  "(occursvari ff i) = False" |
  "(occursvari (var X) i) = (i = X)" |
  "(occursvari (neg f) i) = (occursvari f i)" |
  "(occursvari (and' f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (or f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (diamond act f) i) = (occursvari f i) " |
  "(occursvari (box act f) i) = (occursvari f i)" |
  "(occursvari (nu f) i) = (occursvari f (Suc i))" |
  "(occursvari (mu f) i) = (occursvari f (Suc i))"

lemma notoccursnuandmu [simp] : 
assumes "\<forall>i e. \<not> occursvari (f :: 'a formula) i \<longrightarrow> (formulasemantics f M e = formulasemantics f M (e(i := S')))" 
shows "\<sigma> \<in> {nu, mu} \<Longrightarrow>  \<not> occursvari (\<sigma> f) i \<longrightarrow> (formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
proof-
  assume assum1 : "(\<sigma> :: ('a formula => 'a formula)) \<in> {nu, mu}"
  show "\<not> occursvari (\<sigma> (f :: 'a formula)) i \<longrightarrow> (formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
  proof
    assume assum2: "\<not> occursvari (\<sigma> f) i"
    hence "\<not> occursvari f (Suc i)" using assum1 by (cases "\<sigma> = mu") simp_all      hence "(\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M ((newenvironment e S'') ((Suc i) := S')))" using assms by blast
    hence con1: "\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M (newenvironment (e(i := S')) S'')" by simp
    show "(formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
    proof-
      have con2 : "\<forall>S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M (newenvironment (e(i := S')) S'')" using con1 by auto
      hence "\<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment e S'')} =  \<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment (e(i := S')) S'')}" by auto
      hence "(formulasemantics (nu f) M e = formulasemantics (nu f) M (e(i := S')))" by simp
      moreover have "\<Inter> {S''. S'' \<supseteq> formulasemantics f M (newenvironment e S'')} =  \<Inter> {S''. S'' \<supseteq> formulasemantics f M (newenvironment (e(i := S')) S'')}" using con2 by auto
      from this moreover have "(formulasemantics (mu f) M e = formulasemantics (mu f) M (e(i := S')))" by simp
      ultimately show "(formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))" using assum1 by auto
    qed
  qed
qed

lemma notoccurs [simp] : "(\<not>(occursvari f i) \<longrightarrow> (formulasemantics f M e = formulasemantics f M (e(i := S'))))"
  apply (induct f arbitrary: e i S')
  prefer 9
  using notoccursnuandmu apply blast
  prefer 9
  using notoccursnuandmu apply blast 
  apply (simp_all)
  done

lemma notoccurseqmu :
  assumes "\<not>(occursvari f 0)"
  shows "formulasemantics f M (newenvironment e S') = formulasemantics (mu f) M e"
  apply simp
proof-
  have "\<forall>S''. formulasemantics f M (newenvironment e S') = formulasemantics f M ((newenvironment e S') (0 := S''))" using assms notoccurs by metis
  hence "\<forall>S''. formulasemantics f M ((newenvironment e S'')) = formulasemantics f M (newenvironment e S')" using newenvironmentswitchzero by auto
  hence "\<Inter> {S''. formulasemantics f M (newenvironment e S'') \<subseteq> S''} = \<Inter> {S''. formulasemantics f M (newenvironment e S') \<subseteq> S''}" by blast
  moreover have "... = formulasemantics f M (newenvironment e S')" by auto
  ultimately show "formulasemantics f M (newenvironment e S') = \<Inter> {S'. formulasemantics f M (newenvironment e S') \<subseteq> S'}" by auto
qed

fun closedupuntili :: "'a formula \<Rightarrow> nat \<Rightarrow> bool"
where 
  "(closedupuntili tt i) = True " |
  "(closedupuntili ff i) = True" |
  "(closedupuntili (var X) i) = (X < i)" |
  "(closedupuntili (neg f) i) = (closedupuntili f i)" |
  "(closedupuntili (and' f f') i) = ((closedupuntili f i) \<and> (closedupuntili f' i))" |
  "(closedupuntili (or f f') i) = ((closedupuntili f i) \<and> (closedupuntili f' i))" |
  "(closedupuntili (diamond act f) i) = (closedupuntili f i) " |
  "(closedupuntili (box act f) i) = (closedupuntili f i)" |
  "(closedupuntili (nu f) i) = (closedupuntili f (Suc i))" |
  "(closedupuntili (mu f) i) = (closedupuntili f (Suc i))"

definition closed :: "'a formula \<Rightarrow> bool"
  where "closed f = closedupuntili f 0"

value "closed (mu (var 0))"
value "closed (nu (and' (var 1) (var 0)))"

fun alloccursposneg :: "'a formula \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(alloccursposneg tt b) = True " |
  "(alloccursposneg ff b) = True" |
  "(alloccursposneg (var X) b) = b" |
  "(alloccursposneg (neg f) b) = (alloccursposneg f (\<not>b))" |
  "(alloccursposneg (and' f f') b) = ((alloccursposneg f b) \<and> (alloccursposneg f' b))" |
  "(alloccursposneg (or f f') b) = ((alloccursposneg f b) \<and> (alloccursposneg f' b))" |
  "(alloccursposneg (diamond act f) b) = (alloccursposneg f b) " |
  "(alloccursposneg (box act f) b) = (alloccursposneg f b)" |
  "(alloccursposneg (nu f) b) = (alloccursposneg f b)" |
  "(alloccursposneg (mu f) b) = (alloccursposneg f b)"

fun alloccursposnegupuntili :: "'a formula \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(alloccursposnegupuntili tt i b) = True " |
  "(alloccursposnegupuntili ff i b) = True" |
  "(alloccursposnegupuntili (var X) i b) = ((X \<ge> i) \<or> b)" |
  "(alloccursposnegupuntili (neg f) i b) = (alloccursposnegupuntili f i (\<not>b))" |
  "(alloccursposnegupuntili (and' f f') i b) = ((alloccursposnegupuntili f i b) \<and> (alloccursposnegupuntili f' i b))" |
  "(alloccursposnegupuntili (or f f') i b) = ((alloccursposnegupuntili f i b) \<and> (alloccursposnegupuntili f' i b))" |
  "(alloccursposnegupuntili (diamond act f) i b) = (alloccursposnegupuntili f i b) " |
  "(alloccursposnegupuntili (box act f) i b) = (alloccursposnegupuntili f i b)" |
  "(alloccursposnegupuntili (nu f) i b) = (alloccursposnegupuntili f (Suc i) b)" |
  "(alloccursposnegupuntili (mu f) i b) = (alloccursposnegupuntili f (Suc i) b)"

value "alloccursposneg (mu (var 0)) True"
value "alloccursposneg (nu (and' (neg (var 1)) (var 0))) True"
value "alloccursposneg (nu (and' (neg (var 1)) (var 0))) False"
value "alloccursposnegupuntili (nu (and' (neg (var 1)) (var 0))) 0 True"
value "alloccursposnegupuntili (nu (and' (neg (var 1)) (var 0))) 0 False"

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = formulasemantics f M (newenvironment e S')"

lemma nuX_X : "formulasemantics (nu (var 0)) M e = UNIV"
  apply (simp add: formulasemantics.cases newenvironment.cases)
  done

section \<open>paths\<close>

type_synonym ('a, 's) finpath = "('s \<times> 'a \<times> 's) list"
type_synonym ('a, 's) infpath = "('s \<times> 'a \<times> 's) word"

definition source :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'a" where
"source t = fst t"

definition action :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'b" where
"action t = fst (snd t)"

definition target :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
"target t = snd (snd t)"

fun validfinpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's \<Rightarrow> bool" where
"validfinpath M s [] s' = (s = s')" |
"validfinpath M s (t#ts) s' = (s = source t  \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (source (p 0) = s \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

fun validpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where 
"validpath M s (fin p) = (\<exists>s'. validfinpath M s p s')" |
"validpath M s (inf p) = validinfpath M s p"

definition enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

fun progressing :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M B (fin p) = locked M B (source (p!0))" |
"progressing M B (inf p) = True"

definition match :: "'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> regformtolanguage \<rho>)"

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where 
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

fun occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A (fin p) = (\<exists> a \<in> A. a \<in> (set (map action p)))" |
"occurs A (inf p) = (\<exists> n. (action (p n)) \<in> A)" (*should probably use range*) 

fun occursati :: "'a set \<Rightarrow> nat \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occursati A i (fin p) = (action (p!i) \<in> A)" |
"occursati A i (inf p) = (action (p i) \<in> A)"

fun recursivepath :: "('s \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's" where
"recursivepath succ s 0 = s" | 
"recursivepath succ s (Suc n) = succ (recursivepath succ s n)"

(*negate formulas*)

lemma negtrue : "formulasemantics (neg tt) M e = formulasemantics ff M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negfalse : "formulasemantics (neg ff) M e = formulasemantics tt M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negnegf : "formulasemantics (neg (neg (f))) M e = formulasemantics f M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negand' : "formulasemantics (neg (and' f f')) M e = formulasemantics (or (neg f) (neg f')) M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negor : "formulasemantics (neg (or f f')) M e = formulasemantics (and' (neg f) (neg f')) M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negdiamond : "formulasemantics (neg (diamond act f)) M e = formulasemantics (box act (neg f)) M e"
  apply (simp add: formulasemantics.cases)
  apply auto
  done

lemma negbox : "formulasemantics (neg (box act f)) M e = formulasemantics (diamond act (neg f)) M e"
  apply (simp add: formulasemantics.cases)
  apply auto
  done

lemma complementuniontoexists [simp] : "s \<in> -(\<Union> {S. P S}) = (\<not>(\<exists> S. P S \<and> s \<in> S))"
  apply auto
  done 

lemma intersectiontoforall [simp] : "s \<in> (\<Inter> {S. P S}) = (\<forall> S. P S \<longrightarrow> s \<in> S)"
  apply auto
  done

lemma switchcomplementnegationnu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "formulasemantics (neg (nu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (nu f)) i ) M e"
proof-
have "\<And> S. (formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S))" using assms by blast
moreover have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentsuccessorcomplement)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (nu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (nu f)) i) M e" by simp 
qed

lemma switchcomplementnegationmu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i) M e"
proof-
have "\<And> S. (formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S))" using assms by blast
moreover have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentsuccessorcomplement)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (mu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (mu f)) i) M e" by simp 
qed

lemma negnuinbetween [simp]  : "(formulasemantics (neg (nu f)) M e) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})"
proof-
  have "\<And>s. ((s \<in> (-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)})) = (s \<in> (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S})))"
  proof -
    fix s
    have "(\<forall> S. S \<subseteq> formulasemantics f M (newenvironment e S) \<longrightarrow> s \<notin> S) = (\<forall> S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S) \<longrightarrow> s \<in> S)"
    proof
      assume assum : "\<forall>S. S \<subseteq> formulasemantics f M (newenvironment e S) \<longrightarrow> s \<notin> S"
      show "\<forall>S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S \<longrightarrow> s \<in> S)"
      proof
      fix S
      show "(- formulasemantics f M (newenvironment e (- S)) \<subseteq> S \<longrightarrow> s \<in> S)"
      proof
        assume "- formulasemantics f M (newenvironment e (- S)) \<subseteq> S"
        hence "- S \<subseteq> formulasemantics f M (newenvironment e (- S))" by auto
        thus "s \<in> S" using assum by auto
      qed
      qed
    next
      assume assum : "\<forall>S. -formulasemantics f M (newenvironment e (-S)) \<subseteq> S \<longrightarrow> s \<in> S"
      show "\<forall>S. (S \<subseteq> formulasemantics f M (newenvironment e S)  \<longrightarrow> s \<notin> S)"
      proof
      fix S
      show "(S \<subseteq> formulasemantics f M (newenvironment e S)  \<longrightarrow> s \<notin> S)"
      proof
        assume "S \<subseteq> formulasemantics f M (newenvironment e S)"
        hence h : "(-formulasemantics f M (newenvironment e (S))) \<subseteq> (-S)" by auto
        have "-formulasemantics f M (newenvironment e (-(-S))) \<subseteq> (-S) \<longrightarrow> s \<in> (-S)" using assum by blast
        thus "s \<notin> S" using h by auto
      qed
    qed
  qed
  hence "(\<not>(\<exists> S. S \<subseteq> formulasemantics f M (newenvironment e S) \<and> s \<in> S)) = (\<forall> S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S) \<longrightarrow> s \<in> S)" by auto
  thus "(s \<in> (-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)})) = (s \<in> (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S}))" by simp
qed
  from this have "(-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)}) = (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S})" by blast
    thus ?thesis by (simp add: formulasemantics.cases)
qed

lemma negnu : "formulasemantics (neg (nu f)) M e = formulasemantics (mu (neg (negvari f 0))) M e"
proof-
  have h : "formulasemantics (neg (nu f)) M e = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})" using negnuinbetween by simp
  have "\<forall> e i. (formulasemantics (neg f) M (e(i := -e(i)))) = formulasemantics (negvari (neg f) i) M e"  
  proof
    (induct_tac f)
      show "\<forall> e i. (formulasemantics (neg tt) M (e(i := -e(i)))) =  (formulasemantics (negvari (neg tt) i) M e)" by simp
    next
      show "\<forall> e i. formulasemantics (neg ff) M (e(i := -e(i))) = formulasemantics (negvari (neg ff) i) M e" by auto
    next
      show "\<And>X. \<forall> e i. formulasemantics (neg (var X)) M (e(i := -e(i))) =  formulasemantics (negvari (neg (var X)) i) M e"
        by (simp add: formulasemantics.cases newenvironment.cases negvari.cases)
    next
      show "\<And>f. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) =  formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (neg f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (neg f)) i) M e" by simp
    next 
      show "\<And>f f'. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg f')  M (e(i := -e(i))) = formulasemantics (negvari (neg f') i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (and' f f')) M (e(i := -e(i))) = formulasemantics (negvari (neg (and' f f')) i) M e" by simp
    next 
      show "\<And>f f'. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg f')  M (e(i := -e(i))) = formulasemantics (negvari (neg f') i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (or f f')) M (e(i := -e(i))) = formulasemantics (negvari (neg (or f f')) i) M e" by simp
    next
      show "\<And>act f.\<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (box act f)) M  (e(i := -e(i))) = formulasemantics (negvari (neg (box act f)) i) M e" by simp
    next 
      show "\<And>act f.\<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (diamond act f)) M  (e(i := -e(i))) = formulasemantics (negvari (neg (diamond act f)) i) M e" by simp
    next 
      have "\<And>f. (\<forall>e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e) \<longrightarrow>
        (\<forall> e i. formulasemantics (neg (nu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (nu f)) i ) M e)" using switchcomplementnegationnu by blast
      thus "\<And>f. \<forall>e i. formulasemantics (neg f) M (e(i := - e i)) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall>e i. formulasemantics (neg (nu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (nu f)) i) M e" by simp
    next 
      have "\<And>f. (\<forall>e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e) \<longrightarrow>
        (\<forall> e i. formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i ) M e)" using switchcomplementnegationmu by blast
      thus "\<And>f. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i ) M e" by simp
  qed
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e S)(0 := - (newenvironment e S) 0)) =
     formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by blast
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by (simp only : newenvironmentzerocomplement)  
  hence  "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (neg (negvari f 0)) M (newenvironment e S)" by auto
  hence "(\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))}) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg (negvari f 0)) M (newenvironment e (S)))})" by auto
  thus ?thesis using h by auto
qed

lemma negvarnegvar [simp] : "\<forall>i e. formulasemantics (negvari (negvari f i) i) M e = formulasemantics f M e"
  apply (induct f) 
  apply (simp_all add : formulasemantics.cases)
  done

lemma negmu : "formulasemantics (neg (mu f)) M e = formulasemantics (nu (neg (negvari f 0))) M e"
proof-
  have "\<forall> e. (formulasemantics f M e = formulasemantics (neg (negvari (neg (negvari f 0)) 0)) M e)" by simp
  have h1 : "formulasemantics (neg (mu f)) M e = formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e" by simp
  have "formulasemantics (mu (neg (negvari (neg (negvari f 0)) 0))) M e = formulasemantics (neg (nu (neg (negvari f 0)))) M e" by (simp only: negnu)
  hence h2 : "formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e = formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e" by auto
  also have h3 : "formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e = formulasemantics (nu (neg (negvari f 0))) M e" by (simp add : negnegf)
  thus ?thesis using h1 h2 h3 by auto
qed

(*is not used, because this is ^^*)
fun approximationi :: "('s set \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> nat \<Rightarrow> 's set "
where 
  "approximationi T S 0  = S" | 
  "approximationi T S (Suc i)  = approximationi T (T S) i "

lemma lfp_eq_mu [simp] :
  assumes "mono (transformer f M e)"
  shows  "lfp (transformer f M e) = formulasemantics (mu f) M e"
proof-
  have unfold : "lfp (transformer f M e) = (transformer f M e)(lfp (transformer f M e)) " using assms lfp_unfold by blast
  have lowerbound : "\<forall>S'.(transformer f M e S') \<subseteq> S' \<longrightarrow> lfp (transformer f M e) \<subseteq> S'" using lfp_lowerbound by blast
  have "formulasemantics (mu f) M e =  \<Inter> {S'. S' \<supseteq> (transformer f M e S')}" by (simp add: formulasemantics.cases transformer_def)
  thus ?thesis using unfold lowerbound by (simp add: lfp_def)
qed

lemma transformersubset : 
  assumes "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^i) {} \<subseteq> ((transformer f M e)^^(Suc i)) {}"
  apply (induct i)
  apply (simp)
  using assms apply (simp add : mono_def)
  done

lemma lfp_transformer [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set))){} = lfp (transformer f M e)"
proof-
  have "((transformer f M e)^^(card (UNIV :: 's set))){} = ((transformer f M e)^^Suc(card (UNIV :: 's set))){}"
  proof-
    have "\<exists>n \<le> card(UNIV :: 's set).  ((transformer f M e)^^n) {} = ((transformer f M e)^^(Suc n)) {}"
    proof (rule ccontr)
      assume "\<not> (\<exists>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) {}) = ((transformer f M e ^^ Suc n) {}))"
      hence b: "\<forall>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) {}) \<noteq> ((transformer f M e ^^ Suc n) {})" by auto
      have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((transformer f M e ^^ n) {}) \<ge> n"
      proof
        fix n
        show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) {})"
        proof (induct_tac n)
          show " 0 \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> 0 \<le> card ((transformer f M e ^^ 0) {})" by auto
          fix n
          assume as1: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) {})"
          show "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> Suc n \<le> card ((transformer f M e ^^ Suc n) {})"
          proof-
            have as2: "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card(UNIV :: 's set)" by auto
            hence h1 : "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> (transformer f M e ^^ Suc n) {} \<noteq> (transformer f M e ^^ n) {}" using b by auto
            have h2 : "(transformer f M e ^^ Suc n) {} \<supseteq> (transformer f M e ^^ n) {}" using assms(2) transformersubset by blast 
            have h3 : "finite ((transformer f M e ^^ Suc n) {})" using assms(1) rev_finite_subset by auto
            hence "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> (card ((transformer f M e ^^ Suc n) {}) > card ((transformer f M e ^^ n) {}))" using h1 h2 h3 by (metis psubset_card_mono psubset_eq)
            thus "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> Suc n \<le> card ((transformer f M e ^^ Suc n) {})" using as1 as2 by auto
          qed
        qed
      qed
      hence contradiction1 : "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) {}) \<ge>  Suc (card(UNIV :: 's set))" by auto
      have contradiction2: "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) {}) \<le> card(UNIV :: 's set)" using assms(1) card_mono by auto
      thus False using contradiction1 contradiction2 by auto
    qed
    thus ?thesis by (metis Kleene_iter_lpfp transformersubset assms(2) funpow_decreasing lfp_Kleene_iter lfp_fixpoint order_antisym_conv)
  qed
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma transformer_eq_mu [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set))){} = formulasemantics (mu f) M e"
  using lfp_eq_mu lfp_transformer assms by auto

fun shiftdown :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftdown tt i) = tt " |
  "(shiftdown ff i) = ff" |
  "(shiftdown (var X) i)  = (if X \<le> i then var X else var (X - 1))" |
  "(shiftdown (neg f) i) = neg (shiftdown f i)" |
  "(shiftdown (and' f f') i) = and' (shiftdown f i) (shiftdown f' i) " |
  "(shiftdown (or f f') i) = or (shiftdown f i) (shiftdown f' i)" |
  "(shiftdown (diamond act f) i) = diamond act (shiftdown f i) " |
  "(shiftdown (box act f) i) = box act (shiftdown f i)" |
  "(shiftdown (nu f) i) = nu (shiftdown f (Suc i))" |
  "(shiftdown (mu f) i) = mu (shiftdown f (Suc i))"

lemma shiftupanddown : "shiftdown (shiftup f i) i = f"
  apply (induct f arbitrary : i)
  apply (simp_all)
  done

definition shiftdownenv :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"shiftdownenv e i n = (if n < i then e n else e (n + 1))"

lemma largerandsmaller : "X < i + Suc 0 \<Longrightarrow> X > i \<Longrightarrow> (P :: nat \<Rightarrow> bool) X"
  by auto

lemma largerandsmallerenv [simp] : "X - Suc 0 < i \<longrightarrow> \<not> X \<le> i \<longrightarrow> (s \<in> e 0) = (s \<in> e X)"
  using largerandsmaller by auto

lemma shiftdownnewenv_eq_newenvshiftdown [simp] : "shiftdownenv (newenvironment e S') (Suc i) = newenvironment (shiftdownenv e i) S'"
  apply (rule)
  apply (induct_tac x)
  apply (simp_all add: shiftdownenv_def newenvironment.cases)
  done

lemma inbetweenlemma : "formulasemantics (shiftdown f (Suc i)) M (newenvironment (shiftdownenv e i) S') = 
  formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i))"
  by simp

lemma shiftdownlemma [simp] : "\<not>(occursvari f i) \<longrightarrow> (s \<in> formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (s \<in> formulasemantics f M e)"
  apply (induct f arbitrary: s e i)
  apply (simp_all add: shiftdownenv_def)
  apply (simp_all only : inbetweenlemma)
  apply (simp_all)
  apply (rule impI)
  prefer 2 
  apply (rule impI)
proof-
  fix f s e i
  assume assum1 : "(\<And>s e i. \<not> occursvari f i \<longrightarrow> (s \<in> formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (s \<in> formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "(\<exists>x. x \<subseteq> formulasemantics (shiftdown f (Suc i)) M (newenvironment (shiftdownenv e i) x) \<and> s \<in> x) = (\<exists>x. x \<subseteq> formulasemantics f M (newenvironment e x) \<and> s \<in> x)" by auto
  fix f s e i
  assume assum1 : "(\<And>s e i. \<not> occursvari f i \<longrightarrow> (s \<in> formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (s \<in> formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "(\<forall>x. formulasemantics (shiftdown f (Suc i)) M (newenvironment (shiftdownenv e i) x) \<subseteq> x \<longrightarrow> s \<in> x) = (\<forall>x. formulasemantics f M (newenvironment e x) \<subseteq> x \<longrightarrow> s \<in> x)" by auto
qed

lemma shiftdownnewenv [simp] : "shiftdownenv (newenvironment e S') 0 = e"
  apply (rule)
  apply (simp add: shiftdownenv_def)
done

lemma shiftdowncoro : "\<not>(occursvari f 0) \<longrightarrow> (s \<in> formulasemantics (shiftdown f 0) M e) = (s \<in> formulasemantics f M (newenvironment e S'))" 
  using shiftdownlemma shiftdownnewenv by metis

lemma split : "t = (source t, action t, target t)" 
  by (simp add: source_def action_def target_def)

lemma targetpath [simp]: 
"validfinpath M s p s' \<longrightarrow> s' \<in> insert s (set (map target p))"
  apply (induct p arbitrary : s)
  apply (simp_all)
  done

lemma prop40rtl :
  assumes "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> {act})
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  shows "(s \<in> formulasemantics (mu (and' g (or f (diamond act (var 0))))) (M :: ('a, 's) lts) e)"
  apply (simp add : newenvironment.cases)
proof-
  from assms(1) obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> {act})
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by auto
  show "\<forall>S'. formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S' \<longrightarrow> s \<in> S'"
    apply (rule allI)
    apply (rule impI)
  proof-
  fix S'
  assume assum2 : "formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S'"
  have inS' : "(validfinpath M s p s' \<and> (action ` set p \<subseteq> {act})
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> S') \<longrightarrow> s \<in> S'"
    apply (induct p arbitrary : s)
    apply (simp_all)
    apply (rule impI)
  proof-
    fix t p s
    assume assum3 : "(\<And>s. validfinpath M s p s' \<and> action ` set p \<subseteq> {act} \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S')"
    assume assum4 : "s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t = act \<and> action ` set p \<subseteq> {act} \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S'"
    hence "target t \<in> S'" using assum3 by auto
    hence "(source t, act, target t) \<in> transition M \<and> target t \<in> S'" using assum4 split by metis
    hence c1 : "source t \<in> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assum4 split by auto
    have "source t \<in> formulasemantics (shiftdown g 0) M e" using assum4 by auto
    hence c2 : "source t \<in> formulasemantics g M (newenvironment e S')" using shiftdowncoro assms(3) by metis
    show "source t \<in> S'" using c1 c2 assum2 by auto
  qed
  have "s' \<in> insert s (set (map target p))" using targetpath assum1 by metis
  hence "s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> (formulasemantics (shiftdown f 0) M e)" using assum1 by auto
  hence "s' \<in> formulasemantics g M (newenvironment e S') \<and> s' \<in> formulasemantics f M (newenvironment e S')" using assms(2) assms(3) shiftdowncoro by metis
  hence "s' \<in> S'" using assum2 by auto
  thus "s \<in> S'" using assum1 inS' by auto
qed
qed

lemma prop40ltrinbetween :
  assumes "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  shows "s \<in> ((transformer (and' g (or f (diamond act (var 0)))) M e)^^n){} \<longrightarrow>
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> {act})
     \<and> s \<in> (formulasemantics (shiftdown g 0) M e)
     \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  apply (simp)
  apply (induct n arbitrary : s)
  apply (simp)
  apply (rule impI)
proof-
  fix n s
  assume assum1 : "\<And>s. s \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {} 
    \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act} \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  assume assum2 : "s \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ Suc n) {}"
  hence splitand : "(s \<in> formulasemantics g M (newenvironment e ((transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {}))) 
    \<and> (s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {})) \<or> (\<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {}))" by (simp add: transformer_def formulasemantics.cases)
  hence ing : "s \<in> (formulasemantics (shiftdown g 0) M e)" using shiftdowncoro assms by metis
  from splitand have "s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {})) \<or> (\<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {})" by auto
  moreover {
    assume assum3 : "s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {}))"
    from assum3 have "s \<in> (formulasemantics (shiftdown f 0) M e)" using shiftdowncoro assms by metis
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set [] \<subseteq> {act}) \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set []) \<subseteq> (formulasemantics (shiftdown g 0) M e)" using ing by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act} \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set p) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  moreover {
    assume "\<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {}"
    from this obtain s' where assum3 : "(s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (diamond act (var 0)))) M e ^^ n) {}" by auto
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act}
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" using assum1 by auto
    from this obtain p s'' where tail : "validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act} 
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" by auto
    let ?p = "(s, act, s') # p"
    have "source (s, act, s') = s \<and> (s, act, s') \<in> transition M \<and> validfinpath M (target (s, act, s')) p s''" using assum3 tail by (simp add : source_def target_def)
    hence "validfinpath M s ?p s''" by auto
    hence "validfinpath M s ?p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set ?p \<subseteq> {act}) \<and> 
      s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set ?p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using ing tail by (simp add : target_def action_def)
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act} 
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> {act} 
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using splitand by blast
qed

lemma prop40ltr :
  assumes "s \<in> formulasemantics (mu (and' g (or (f) (diamond act (var 0))))) (M :: ('a, 's) lts) e"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "(finite (UNIV :: 's set))"
    and "mono (transformer (and' g (or f (diamond act (var 0)))) M e)" (*deze moet nog weg*)
  shows "(\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) 
        \<and> (set (map action p) \<subseteq> {act}) 
        \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (simp add : newenvironment.cases)
proof-
  have "s \<in> ((transformer (and' g (or f (diamond act (var 0)))) M e)^^(card (UNIV :: 's set))){}" using assms(1) assms(4) assms(5) transformer_eq_mu by auto 
  thus "\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> formulasemantics (shiftdown f 0) M e
        \<and> action ` set p \<subseteq> {act}
        \<and> s \<in> formulasemantics (shiftdown g 0) M e
        \<and> target ` set p \<subseteq> formulasemantics (shiftdown g 0) M e" using  prop40ltrinbetween assms(2) assms(3) by metis
qed

(*to do: include mono and extended diamond
also simplifies dependence to not occurs*)
lemma prop40 :
  assumes "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "(finite (UNIV :: 's set))"
    and "mono (transformer (and' g (or f (diamond a (var 0)))) M e)" (*deze moet nog weg*)
  shows "(s \<in> formulasemantics (mu (and' g (or f (diamond a (var 0))))) (M :: ('a, 's) lts) e) = 
    (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> {a}) 
      \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (rule)
  using assms prop40ltr apply (metis)
  using assms prop40rtl apply (metis)
  done