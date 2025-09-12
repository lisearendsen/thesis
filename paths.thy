theory paths
imports syntaxsemantics
begin

text \<open>We define finite paths as lists of transitions
and infinite paths as mappings from natural numbers to transitions.\<close>

type_synonym ('a, 's) finpath = "('s \<times> 'a \<times> 's) list"
type_synonym ('a, 's) infpath = "('s \<times> 'a \<times> 's) word"

text \<open>A transition can be splitted into its source, action, and target.\<close>

definition source :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'a" where
"source t = fst t"

definition action :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'b" where
"action t = fst (snd t)"

definition target :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
"target t = snd (snd t)"

lemma sourceactiontargetsimp [simp] :
  shows "source (s, a, s') = s"
  and "action (s, a, s') = a"
  and "target (s, a, s') = s'"
  by (simp_all add: source_def action_def target_def)

lemma splittransition [simp] : "(source t, action t, target t) = t"
  by (simp add: source_def action_def target_def)

text \<open>Then we define the notion of valid paths, a finite path is valid with respect to its first 
state and last state, while an infinite path is valid only with respect to its first state.\<close>

fun validfinpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's \<Rightarrow> bool" where
"validfinpath M s [] s' = (s = s')" |
"validfinpath M s (t#ts) s' = (s = source t  \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (s = source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

text \<open>A path is either a finite path or an infinite path.\<close>

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

text \<open>Define predicate of progressing paths.\<close>

definition enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"

definition enabled :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> bool" where
"enabled M s \<alpha> = (\<exists> a \<in> \<alpha>. a \<in> enabledactions M s)"

lemma actionenabled : "enabledactions M s \<noteq> {} = (\<exists>a s'. (s, a, s') \<in> transition M)"
  by (simp add: enabledactions_def)

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

lemma lockednegenabled : "locked M B s = (\<not> enabled M s (-B))" 
  by (auto simp: locked_def enabled_def)

fun progressing :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M s B (fin p) = (\<exists>s'. validfinpath M s p s' \<and> locked M B s')" |
"progressing M s B (inf p) = validinfpath M s p"

text \<open>A finite path matches a regular formula if and only if its sequence of actions is in the language 
of the regular formula.\<close>

definition match :: "'a rexp \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> lang \<rho>)"

text \<open>A finite path matches a regular formula n times if and only if its sequence of actions is in the 
language of the regular formula concatenated n times.\<close>

fun matchntimes :: "nat \<Rightarrow> 'a rexp \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"matchntimes 0 R p = (p = [])" |
"matchntimes (Suc n) R p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')"

lemma existsninduct [simp] : "((\<exists>n. P (Suc n)) \<or> P 0) = (\<exists>n. P n)"
  using zero_induct by auto

text \<open>A finite path \<open>p\<close> matches \<open>Star R\<close> (Kleene star) if and only if there exists \<open>n\<close> such that 
\<open>p\<close> matches \<open>R\<close> \<open>n\<close> times.\<close>

lemma matchstar_eq_matchntimes [simp] : "match (Star R) p = (\<exists>n. matchntimes n R p)"
proof-
  have "match (Star R) p = (map action p \<in> (\<Union>n. (lang R) ^^ n))" by (simp add: match_def star_def)
  moreover have "... = (\<exists>n. map action p \<in> (lang R) ^^ n)" by auto
  moreover have "\<forall>n. (map action p \<in> (lang R) ^^ n) = (matchntimes n R p)"
  proof
    fix n
    show "(map action p \<in> (lang R) ^^ n) = (matchntimes n R p)"
    apply (induct n arbitrary : p; simp)
    proof-
    fix n
    fix p :: "('a, 's) finpath"
    assume assum1 : "(\<And>(p :: ('a, 's) finpath). (map action p \<in> lang R ^^ n) = matchntimes n R p)"
    have "(map action p \<in> lang R @@ lang R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and>  ((map action p') \<in> lang R) \<and> ((map action p'') \<in> lang R ^^ n))" by (rule exists_map_abinconc)
    moreover have "... = (\<exists>p' p''. p = p'@p'' \<and>  match R p' \<and>  matchntimes n R p'')" using assum1 by (auto simp: match_def) 
    ultimately show "(map action p \<in> lang R @@ lang R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')" by simp
  qed
  qed
  ultimately show ?thesis by blast
qed

text \<open>Simplifications of match for all patterns of regular formulas.\<close>

lemma matchunfold [simp] : 
  shows "match Zero p = False"
  and "match One p = (p = [])"
  and "match (Atom a) p = (\<exists>t. p = [t] \<and> action t = a)"
  and "match (Plus R Q) p = (match R p \<or> match Q p)"
  and "match (Times R Q) p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> match Q p'')"
  apply (simp_all add: match_def exists_map_abinconc)
  apply (rule iffI; auto)
  done

lemma matchunfoldActslist [simp] : "match (Actslist A) p = (\<exists>t. p = [t] \<and> action t \<in> set A)"
  by (induct A; auto)

lemma matchunfoldActs [simp] : "finite A \<Longrightarrow> match (Acts A) p = (\<exists>t. p = [t] \<and> action t \<in> A)"
  by (simp add: Acts_def; rule someI2_ex; simp add: finite_list)

text \<open>A finite path matches \<open>Star (Acts A)\<close> (A Kleene star) if and only if 
  all its actions are in \<open>A\<close>.\<close>

lemma matchstaract : "finite A \<Longrightarrow> match (Star (Acts A)) p = (set (map action p) \<subseteq> A)"
  apply (induct p; simp)
  apply (subgoal_tac "matchntimes 0 (Acts A) []")
  apply blast
  apply simp
proof
  fix t 
  fix p :: "('a, 's) finpath"
  assume assum1: "(\<exists>n. matchntimes n (Acts A) p) = (action ` set p \<subseteq> A)"
  assume assum2 : "finite A"
  assume "\<exists>n. matchntimes n (Acts A) (t # p)"
  from this obtain n where "matchntimes n (Acts A) (t # p)" by auto
  thus "action t \<in> A \<and> action ` set p \<subseteq> A" 
    apply (induct n)
    using assum1 assum2 apply auto
    done
next
  fix t :: "'s \<times> 'a \<times> 's" 
  fix p :: "('a, 's) finpath"
  assume "(\<exists>n. matchntimes n (Acts A) p) = (action ` set p \<subseteq> A)"
  from this obtain n where assum1: "matchntimes n (Acts A) p = (action ` set p \<subseteq> A)" by auto
  assume assum2: "finite A"
  assume "action t \<in> A \<and> action ` set p \<subseteq> A"
  hence "t # p = [t] @ p \<and> action t \<in> A \<and> matchntimes n (Acts A) p" using assum1 by simp
  hence "matchntimes (Suc n) (Acts A) (t # p)" unfolding matchntimes.simps using matchunfoldActs assum2 by blast
  thus "\<exists>n. matchntimes n (Acts A) (t # p)" by blast
qed

text \<open>Defining operations on paths and some simplifications for these operations.\<close>

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where 
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

lemma emptylist [simp] : "(pref i p = []) = (i = 0 \<or> p = fin [])"
  using take_eq_Nil by (cases p) simp_all

lemma nosuffix : "(p = fin [] \<or> i = 0) \<Longrightarrow> (suff i p = p)"
  by (cases p; auto)

fun indicespath :: "('a, 's) path \<Rightarrow> nat set" where
"indicespath (fin p) = ({n. n < length p})" |
"indicespath (inf p) = UNIV"

abbreviation laststate :: "('a, 's) finpath \<Rightarrow> 's" where
"laststate p \<equiv> target (last p)"

lemma laststatesimps [simp]:
  shows "p = [] \<Longrightarrow> laststate (t # p) = target t "
  and "p \<noteq> [] \<Longrightarrow> laststate (t # p) = laststate p"
  by simp_all
  
lemma validfinpathlaststate : "p \<noteq> [] \<and> validfinpath M s p s' \<Longrightarrow> laststate p = s'"
  by (induct p arbitrary : s; auto)

lemma prefleft : "n \<in> indicespath p \<Longrightarrow> (pref (Suc n) p) = (ind 0 p) # (pref n (suff (Suc 0) p))"
  by (cases p; induct n; simp add: take_Suc_conv_app_nth)

text \<open>Simplifications for valid paths, in particular on extensions and subpaths.\<close>

lemma validfinpathsplit [simp] : "validfinpath M s (p @ p') s' = (\<exists>s''. validfinpath M s p s'' \<and> validfinpath M s'' p' s')"
  by (induct p arbitrary: s; simp)

lemma shiftinfvalidpath [simp]: "validinfpath M s (t ## p) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)"
proof-
  have "(\<forall>n. (n = 0 \<longrightarrow> t \<in> transition M \<and> target t = source (p 0)) \<and> (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))) =
    (t \<in> transition M \<and> target t = source (p 0) \<and> (\<forall>n. (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))))" by auto
  moreover have "... = (t \<in> transition M \<and> target t =  source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> target (p n) = source (p (Suc n))))" by auto
  ultimately have "(validinfpath M s (conc [t] p)) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)" by (simp add: validinfpath_def conc_def)
  thus ?thesis by simp
qed

lemma validinfpathsplit [simp] : "validinfpath M s (conc p p') = (\<exists>s'. validfinpath M s p s' \<and> validinfpath M s' p')"
  by (induct p arbitrary: s; simp)

lemma validfinsubpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M s (take i p) (source (p!i))"
  apply (induct p arbitrary: s i)
  apply (simp)
proof-
  case Cons
  then show ?case by (cases i) auto
qed

lemma validfinsubpathright [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M (source (p!i)) (drop i p) s'"
  apply (induct p arbitrary: s i)
  apply (simp)
proof-
  case Cons
  then show ?case by (cases i) auto
qed
 
lemma validinfsubpath : "validinfpath M s p \<Longrightarrow> (validfinpath M s (prefix i p) (source (p i)))"
  by (induct i arbitrary : s p; simp add: validinfpath_def)

lemma validinfsubpathright [simp] : "validinfpath M s p \<Longrightarrow> validinfpath M (source (p i)) (suffix i p)"
  by (induct i; simp add: validinfpath_def)

lemma zerothtransitionfinpath : "0 < length p \<and> validfinpath M s p s' \<Longrightarrow> (p!0 \<in> transition M)"
  by (induct p; simp)

text \<open>The \<open>i\<close>'th transition in a valid path is in the transitions of the labeled transition system\<close>

lemma ithtransitionfinpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> (p!i \<in> transition M)"
proof-
  assume assum1: "i < length p \<and> validfinpath M s p s'"
  hence "0 < length (drop i p) \<and> validfinpath M (source (p!i)) (drop i p) s'" by auto
  hence "(drop i p)!0 \<in> transition M" by (rule zerothtransitionfinpath)
  moreover have "(drop i p)!0 = p!i" using assum1 by auto
  ultimately show ?thesis by simp
qed

lemma validfinpathsource : "p \<noteq> [] \<and> validfinpath M s p s' \<longrightarrow> s = source (p!0)"
  by (induct p arbitrary : s; simp)

lemma zerothtargetsourcefinpath : "Suc 0 < length p \<and> validfinpath M s p s' \<Longrightarrow> target (p!0) = source (p!(Suc 0))"
  by (induct p; auto simp : validfinpathsource)

lemma ithtargetsourcefinpath [simp] : "Suc i < length p \<and> validfinpath M s p s' \<Longrightarrow> target (p!i) = source (p!(Suc i))"
proof-
  assume assum1: "Suc i < length p \<and> validfinpath M s p s'"
  hence "Suc 0 < length (drop i p) \<and> validfinpath M (source (p!i)) (drop i p) s'" by auto
  hence "target ((drop i p)!0) = source ((drop i p)!(Suc 0))" by (rule zerothtargetsourcefinpath)
  moreover have "(drop i p)!0 = p!i \<and> (drop i p)!(Suc 0) = p!(Suc i)" using assum1 by auto
  ultimately show ?thesis by simp
qed

text \<open>Defining notions of occurence.
A set of actions \<open>A\<close> occurs on path \<open>p\<close> if and only if there exists an action in A 
that occurs along the path.\<close>

fun occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A (fin p) = (\<exists> a \<in> A. a \<in> set (map action p))" |
"occurs A (inf p) = (\<exists> a \<in> A. a \<in> image action (range p))"

lemma occursfinalternative : "occurs A (fin p) = (\<exists>n < length p. action (p!n) \<in> A)"
  apply (simp add: image_iff)
  using in_set_conv_nth apply metis
  done

lemma occursinfalternative : "occurs A (inf p) = (\<exists> n. action (p n) \<in> A)"
  by auto

lemma sourcetargetfin : "validfinpath M s p s' \<Longrightarrow>  insert s (set (map target p)) = insert s' (set (map source p))"
  by (induct p arbitrary: s; auto)

lemma sourcetargetinf : "validinfpath M s p \<Longrightarrow> insert s (image target (range p)) = image source (range p)"
  apply (rule set_eqI)
  apply (simp add: validinfpath_def image_iff)
  using nat.exhaust apply metis  
  done

fun occursstate :: "'s set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occursstate S' s (fin p) = (\<exists> s' \<in> S'. s' \<in> insert s (set (map target p)))" |
"occursstate S' s (inf p) = (\<exists> s' \<in> S'. s' \<in> insert s (image target (range p)))"

lemma occursstatealternative : "occursstate S' s p = (s \<in> S' \<or> (\<exists> n \<in> indicespath p. target (ind n p) \<in> S'))"
  apply (cases p; simp add: image_iff)
  using in_set_conv_nth apply metis
  apply auto
  done

text \<open>Defining the extension of a finite path.\<close>

fun extendfinpath :: "('a, 's) finpath \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where
"extendfinpath p (fin p') = fin (p @ p')" |
"extendfinpath p (inf p') = inf (conc p p')"

lemma extendfinemptypath [simp] : "(extendfinpath [] p) = p"
  by (cases p; simp)

lemma occursleft : "occurs S' (fin p) \<Longrightarrow> occurs S' (extendfinpath p p')"
  by (cases p'; auto)

lemma occursright : "occurs S' p' \<Longrightarrow> occurs S' (extendfinpath p p')"
  by (cases p'; auto)

lemma occursstateleft: "occursstate S' s (fin p) \<Longrightarrow> (occursstate S' s (extendfinpath p p'))"
  by (cases p'; auto)
                                                      
lemma occursstateright : "p \<noteq> [] \<and> occursstate S' (laststate p) p' \<Longrightarrow> occursstate S' s (extendfinpath p p')"
  apply (cases p'; subgoal_tac "p \<noteq> [] \<longrightarrow> occursstate {laststate p} s (extendfinpath p p')"; induct p; simp)
  apply blast+
  done

lemma occursstaterightvalidpath : "validfinpath M s p s' \<and> occursstate S' s' p' \<Longrightarrow> occursstate S' s (extendfinpath p p')"
proof-
  assume assum1 : "validfinpath M s p s' \<and> occursstate S' s' p'"
  hence "p = [] \<Longrightarrow> occursstate S' s (extendfinpath p p')" by simp
  moreover have "p \<noteq> [] \<Longrightarrow> occursstate S' s (extendfinpath p p')" using assum1 occursstateright validfinpathlaststate by metis
  ultimately show ?thesis by blast  
qed

lemma occursempty : "occurs A (fin p) \<Longrightarrow> p \<noteq> []"
  by (induct p; simp)

lemma occursstateempty : "occursstate S' s (fin p) \<and> s \<notin> S' \<Longrightarrow> p \<noteq> []"
  by (induct p; simp)

text \<open>Defining violating paths, using \<open>freeuntiloccurrence\<close>.\<close>

definition freeuntiloccurrence :: "('a, 's) path \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e = ((\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (pref i p))) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)
  \<or> \<not>(occurs \<alpha>\<^sub>f p))"

definition violating :: "('a, 's) path \<Rightarrow> 'a rexp \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)"

lemma violatingempty [simp] : "violating p One \<alpha>\<^sub>f \<alpha>\<^sub>e = freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e"
proof-
  have "violating p One \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. (pref i p) = [] \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by (simp add : match_def violating_def)
  moreover have "... = (\<exists>i. (i = 0 \<or> p = fin []) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by auto
  moreover have "... = (freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e)" using nosuffix by metis
  ultimately show ?thesis by auto
qed

text \<open>Definition of \<open>freeuntiloccurrence\<close> does not specify that \<open>i\<close> is within the length of the path.
But if the action occurs only outside the bound, then it does not occur.\<close>

lemma occursoutsidebound : 
  assumes "\<exists>i \<ge> length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p'!i) \<in> \<alpha>\<^sub>e"
  shows "\<not> occurs \<alpha>\<^sub>f (fin p')"
  using assms take_all by metis

lemma freeuntiloccurrence_inbound : "freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<not> occurs \<alpha>\<^sub>f p \<or> (\<exists>i \<in> indicespath p. \<not>occurs \<alpha>\<^sub>f (fin (pref i p)) \<and> action (ind i p) \<in> \<alpha>\<^sub>e))"
  apply (cases p; simp add: freeuntiloccurrence_def del: occurs.simps)
  using occursoutsidebound leI apply blast+
  done

text \<open>The existence of a progressing path that is \<open>\<alpha>\<^sub>f\<close> free until occurrence of \<open>\<alpha>\<^sub>e\<close> can be split into 4 cases.\<close>

lemma freeuntiloccurrence_cases :
  shows "freeuntiloccurrence (fin p) \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<not> occurs \<alpha>\<^sub>f (fin p) \<or> (\<exists>i < length p. \<not>(occurs \<alpha>\<^sub>f (fin (take i p))) \<and> action (p!i) \<in> \<alpha>\<^sub>e))"
  and "freeuntiloccurrence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<not> occurs \<alpha>\<^sub>f (inf p')  \<or> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e))"
  apply (simp_all only: freeuntiloccurrence_inbound)
  apply simp_all
  done

lemma freeuntiloccurrenceprogressing_cases [simp] : 
  shows "(freeuntiloccurrence (fin p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin p)) = 
   (\<exists>s'. validfinpath M s p s' \<and> locked M B s' \<and> (\<not> occurs \<alpha>\<^sub>f (fin p) \<or> (\<exists>i < length p. \<not>(occurs \<alpha>\<^sub>f (fin (take i p))) \<and> action (p!i) \<in> \<alpha>\<^sub>e)))"
  and "(freeuntiloccurrence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf p')) = 
   (validinfpath M s p' \<and> (\<not> occurs \<alpha>\<^sub>f (inf p') \<or> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
  apply (simp_all only: freeuntiloccurrence_cases)
  apply auto
  done

lemma existfreeuntiloccurrenceprogressing_cases [simp] : "(\<exists> p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
 ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
  (is "?L = ?R")
proof
  assume ?L
  from this obtain p where assum1: "freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by auto
  {
    fix finp
    assume "p = fin finp"
    hence "freeuntiloccurrence (fin finp) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin finp)" using assum1 by simp
    hence ?R by (simp only: freeuntiloccurrenceprogressing_cases; blast)
  }
  moreover {
    fix infp
    assume "p = inf infp"
    hence "freeuntiloccurrence (inf infp) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf infp)" using assum1 by simp
    hence ?R by (simp only: freeuntiloccurrenceprogressing_cases; blast)
  }
  ultimately show ?R by (rule path.exhaust; simp)
next
  show "?R \<Longrightarrow> ?L" using freeuntiloccurrenceprogressing_cases by meson
qed

lemma prefixextendinfpath [simp]: "prefix (Suc i) (t ## p) = t # (prefix i p)"
  by (induct i; simp)

lemma invariantextension : 
  assumes "(\<nexists>p s''. validfinpath M s p s'' \<and> enabledactions M s'' = {})"
  shows "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>p s''. validfinpath M s' p s'' \<and> enabledactions M s'' = {})"
proof-
  have "validfinpath M s [] s" by simp
  hence "enabledactions M s \<noteq> {}" using assms by blast
  from this obtain a s' where res1 : "(s, a, s') \<in> transition M" using actionenabled by metis
  let ?t = "(s, a, s')"
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> enabledactions M s'' = {}"
  proof
    assume "\<exists>p s''. validfinpath M s' p s'' \<and> enabledactions M s'' = {}"
    from this obtain p s'' where "validfinpath M s' p s'' \<and> enabledactions M s'' = {}" by auto
    hence "validfinpath M s (?t # p) s'' \<and> enabledactions M s'' = {}" using res1 by simp
    thus False using assms by blast
  qed
  thus ?thesis using res1 by auto
qed

lemma invariantextension' : 
  assumes "\<forall>s. (enabledactions M s = {}) \<longrightarrow> P s"
  and "(\<nexists>p s''. validfinpath M s p s'' \<and> P s'')"
  shows "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>p s''. validfinpath M s' p s'' \<and> P s'')"
proof-
  have "enabledactions M s \<noteq> {}"
  proof
    assume "enabledactions M s = {}"
    hence "validfinpath M s [] s \<and> P s" using assms(1) by simp
    thus False using assms(2) by blast
  qed
  from this obtain a s' where res1 : "(s, a, s') \<in> transition M" using actionenabled by metis
  let ?t = "(s, a, s')"
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> P s''"
  proof
    assume "\<exists>p s''. validfinpath M s' p s'' \<and> P s''"
    from this obtain p s'' where "validfinpath M s' p s'' \<and> P s''" by auto
    hence "validfinpath M s (?t # p) s'' \<and> P s''" using res1 by simp
    thus False using assms(2) by blast
  qed
  thus ?thesis using res1 by auto
qed

text \<open>Defining functions to structurally create infinite paths (that are fair)\<close>

lemma validinfpathsplitlaststate : "p \<noteq> []  \<Longrightarrow> (validfinpath M s p (laststate p) \<and> validinfpath M (laststate p) p') = validinfpath M s (conc p p')"
  using validinfpathsplit validfinpathlaststate by metis

function recursiveconcpaths :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's \<times> 'a \<times> 's" where
"recursiveconcpaths succ s n = (if succ s = [] then undefined else (if n < length (succ s) then (succ s)!n else (recursiveconcpaths succ (laststate (succ s)) (n - length (succ s)))))"
  by auto
termination 
  apply (relation "measure (\<lambda>(succ,s,n). n)")
  apply auto
  apply (subgoal_tac "n > 0")
  apply simp
  using length_greater_0_conv apply fastforce
  done

fun ithpath :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> ('a, 's) finpath" where
"ithpath succ s 0 = succ s" |
"ithpath succ s (Suc i) = succ (laststate (ithpath succ s i))"

lemma ithpath_right : "ithpath succ s (Suc i) = ithpath succ (laststate (succ s)) i"
  by (induct i; simp)

fun concipaths :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> ('a, 's) finpath" where
"concipaths succ s 0 = []" |
"concipaths succ s (Suc i) = succ s @ concipaths succ (laststate (succ s)) i"

lemma concipaths_right : "concipaths succ s (Suc i) = concipaths succ s i @ ithpath succ s i"
  apply (induct i arbitrary: s)
  apply (simp)
  apply (simp add: ithpath_right del: ithpath.simps)
  done

lemma ithpath_somesucc : 
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. laststate (succ s) \<in> S')"
  shows "\<exists>s' \<in> S'. ithpath succ s i = succ s'"
  by (induct i; auto simp: assms)

lemma ithpath_laststate :
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. laststate (succ s) \<in> S')"
  shows "laststate (ithpath succ s i) \<in> S'"
  by (induct i; simp add: assms)

lemma predicate_ithpath : 
  assumes "P (succ s) \<and> s \<in> S' \<and> (\<forall>s \<in> S'. P (succ s) \<longrightarrow> P (succ (laststate (succ s))) \<and> laststate (succ s) \<in> S')"
  shows "P (ithpath succ s i)"
  apply (induct i)
  apply (simp add: assms)
proof-
  fix i
  have "P (ithpath succ s (Suc i)) \<and> laststate (ithpath succ s i) \<in> S'" by (induct i; simp add: assms)
  thus "P (ithpath succ s (Suc i))" by (simp add: assms)
qed

lemma ithpath_notempty : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate (succ s) \<in> S') \<longrightarrow> ithpath succ s i \<noteq> []"
  apply (induct i arbitrary : s)
  apply simp
  using ithpath_right apply metis
  done

lemma allithpath_notempty : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate (succ s) \<in> S') \<Longrightarrow> (\<forall>j < i. ithpath succ s j \<noteq> [])"
  using ithpath_notempty by metis

lemma lengthconcipaths : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<longrightarrow> (length (concipaths succ s i)) \<ge> i"
  apply (induct i)
  apply simp
  apply (simp only : concipaths_right)
proof
  fix i
  assume IH : "(\<forall>j<i. ithpath succ s j \<noteq> []) \<longrightarrow> i \<le> length (concipaths succ s i)"
  assume assum1 : "\<forall>j<Suc i. ithpath succ s j \<noteq> []"
  hence "i \<le> length (concipaths succ s i)" using IH by auto
  moreover have "Suc 0 \<le> length (ithpath succ s i)" by (simp add: leI assum1)
  ultimately show "Suc i \<le> length (concipaths succ s i @ ithpath succ s i)" by auto
qed

lemma recursiveconcpaths_ithpath : "m = length (concipaths succ s i) \<and> k < length (ithpath succ s i) \<and> (\<forall>j \<le> i. ithpath succ s j \<noteq> []) \<Longrightarrow> recursiveconcpaths succ s (m + k) = (ithpath succ s i) ! k"
  apply (induct i arbitrary : m s)
  apply simp
proof-
  fix i m s
  assume IH : "(\<And>m s. m = length (concipaths succ s i) \<and> k < length (ithpath succ s i) \<and>  (\<forall>j\<le>i. ithpath succ s j \<noteq> []) \<Longrightarrow> recursiveconcpaths succ s (m + k) = ithpath succ s i ! k)" 
  assume assum1: "m = length (concipaths succ s (Suc i)) \<and> k < length (ithpath succ s (Suc i)) \<and> (\<forall>j\<le>Suc i. ithpath succ s j \<noteq> [])"
  hence "m + k \<ge> length (succ s) \<and> succ s \<noteq> []" by auto
  hence "recursiveconcpaths succ s (m + k) = recursiveconcpaths succ (laststate (succ s)) ((m - length (succ s)) + k)" using assum1 by auto
  moreover have "... = ithpath succ (laststate (succ s)) i ! k"
    apply (rule IH)
    using assum1 apply auto
    using ithpath_right assum1 Suc_le_mono apply metis+
    done
  moreover have "... = ithpath succ s (Suc i) ! k" by (simp only: ithpath_right)
  ultimately show "recursiveconcpaths succ s (m + k) = ithpath succ s (Suc i) ! k" by simp
qed

lemma take_all_but_last : "l \<noteq> [] \<Longrightarrow> (take (length l - 1) l) @ [l ! (length l - 1)] = l" 
proof-
  assume assum1: "l \<noteq> []"
  hence "(take (length l - 1) l) @ [l ! (length l - 1)] = (take (length l - 1) l) @ [hd (drop (length l - 1) l)]" by (simp add: hd_drop_conv_nth)
  moreover have "... = l" by (simp add: take_hd_drop assum1)
  ultimately show ?thesis by simp
qed

lemma subsequence_eq_list : "length l = (j - i) \<and> (\<forall>k. k\<ge>i \<and> k<j \<longrightarrow> w k = l!(k - i)) \<Longrightarrow> subsequence w i j = l"
  apply (simp add: subsequence_def)
  apply (induct j arbitrary: l; simp)
  apply auto
proof-
  fix j 
  fix l :: "'a list"
  assume IH : "(\<And>l'. length l' = j - i \<and> (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> l ! (k - i) = l' ! (k - i)) \<Longrightarrow> map w [i..<j] = l')"
  assume assum1: "length l = Suc j - i"
  hence "length (take (j - i) l) = j - i" by auto
  moreover have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> l ! (k - i) = (take (j - i) l) ! (k - i)" by auto
  ultimately have "map w [i..<j] = take (j - i) l" using IH by metis
  hence "map w [i..<j] @ [l ! (j - i)] = (take (j - i) l) @ [l ! (j - i)]" by auto
  moreover assume "i \<le> j"
  ultimately have "l \<noteq> [] \<and> map w [i..<j] @ [l ! (j - i)] = (take (length l - 1) l) @ [l ! (length l - 1)]" using assum1 by auto
  thus "map w [i..<j] @ [l ! (j - i)] = l" using assum1 take_all_but_last by metis
qed
  
lemma subsequence_recursiveconcpaths : "n = length (concipaths succ s i) \<and> k = length (ithpath succ s i) \<and> (\<forall>j \<le> i. ithpath succ s j \<noteq> []) \<Longrightarrow> subsequence (recursiveconcpaths succ s) n (n + k) = ithpath succ s i"
  apply (rule subsequence_eq_list)
proof-
  assume assum1: "n = length (concipaths succ s i) \<and> k = length (ithpath succ s i) \<and> (\<forall>j\<le>i. ithpath succ s j \<noteq> [])"
  have "(\<forall>m. n \<le> m \<and> m < n + k \<longrightarrow> recursiveconcpaths succ s m = ithpath succ s i ! (m - n))"
    apply (rule allI)
  proof
    fix m
    assume assum2: "n \<le> m \<and> m < n + k"
    hence "m - n < length (ithpath succ s i)" using assum1 by auto
    hence "recursiveconcpaths succ s (n + (m - n)) = (ithpath succ s i) ! (m - n)" using recursiveconcpaths_ithpath assum1 by metis
    thus "recursiveconcpaths succ s m = ithpath succ s i ! (m - n)" by (simp add: assum2)
  qed
  thus "length (ithpath succ s i) = n + k - n \<and> (\<forall>m. n \<le> m \<and> m < n + k \<longrightarrow> recursiveconcpaths succ s m = ithpath succ s i ! (m - n))" using assum1 by auto
qed

lemma existsconcipaths : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<Longrightarrow> concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)"
  apply (induct i arbitrary: s)
  apply simp
  apply (simp only: concipaths_right)
proof-
  fix i s
  assume IH : "(\<And>s. (\<forall>j<i. ithpath succ s j \<noteq> []) \<Longrightarrow> concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s))"
  assume assum1 : "(\<forall>j<Suc i. ithpath succ s j \<noteq> [])"
  hence "prefix (length (concipaths succ s i)) (recursiveconcpaths succ s) = concipaths succ s i" using IH by auto
  moreover have "prefix (length (concipaths succ s i @ ithpath succ s i)) (recursiveconcpaths succ s) = 
    (prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)) @ (subsequence (recursiveconcpaths succ s) (length (concipaths succ s i)) (length (concipaths succ s i) + length (ithpath succ s i)))" 
    by (simp add: subsequence_append)
  moreover have "(subsequence (recursiveconcpaths succ s) (length (concipaths succ s i)) (length (concipaths succ s i) + length (ithpath succ s i))) = ithpath succ s i"
    by (simp add: assum1 subsequence_recursiveconcpaths)
  ultimately show "concipaths succ s i @ ithpath succ s i = prefix (length (concipaths succ s i @ ithpath succ s i)) (recursiveconcpaths succ s)" by auto
qed

lemma concipaths_nth : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<and> n < i \<Longrightarrow> (concipaths succ s i) ! n = recursiveconcpaths succ s n"
proof-
  assume assum1 : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<and> n < i"
  hence length : "length (concipaths succ s i) \<ge> i " by (simp add: lengthconcipaths)
  moreover have "concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)" using assum1 existsconcipaths by metis
  ultimately have "(concipaths succ s i) ! n = (prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)) ! n" by simp
  moreover have "... = recursiveconcpaths succ s n" using length assum1 by auto
  ultimately show ?thesis by simp
qed
 
lemma unfoldrecursiveconcpaths  : 
  assumes "succ s \<noteq> []"
  shows "recursiveconcpaths succ s = conc (succ s) (recursiveconcpaths succ (laststate (succ s)))"     
  using assms by auto

lemma source_eq_target :
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (source ((succ s) ! 0)) = s \<and> laststate (succ s) \<in> S')"
  shows "laststate (ithpath succ s n) \<in> S' \<and> source ((ithpath succ s (Suc n)) ! 0) = laststate (ithpath succ s n)"
  apply (induct n)
  apply (simp add: assms)
  unfolding ithpath.simps using assms apply blast
  done

lemma lasttarget_eq_targetithpath : 
  assumes "ithpath succ s n \<noteq> []"
  shows "laststate (concipaths succ s (Suc n)) = laststate (ithpath succ s n)"
  by (simp add: concipaths_right assms del: concipaths.simps)

lemma laststate_suc :
  "((\<lambda>s. laststate (succ s)) ^^ Suc n) s = ((\<lambda>s. laststate (succ s)) ^^ n) (laststate (succ s))"
  by (induct n; simp)

lemma source_ithpath_eqlaststate :
  assumes "\<forall>s \<in> S'. source (succ s ! 0) = s \<and> laststate (succ s) \<in> S'"
  shows "s \<in> S' \<longrightarrow> source (ithpath succ s n ! 0) = ((\<lambda>s. laststate (succ s)) ^^ n) s"
  apply (induct n arbitrary: s)
  apply (simp add: assms) 
  apply (simp only: ithpath_right)
  using laststate_suc assms apply metis
  done

lemma source_ithpath_eqtarget_Suc : 
   "ithpath succ s n \<noteq> [] \<and> validfinpath M s' (ithpath succ s n) s'' \<Longrightarrow> ((\<lambda>s. laststate (succ s)) ^^ (Suc n)) s = s''"
  apply (induct n arbitrary: s)
  apply simp
  using validfinpathlaststate apply meson
  apply (simp only: laststate_suc)
  apply (simp add: ithpath_right del: ithpath.simps)
  done

lemma source_ithpath_eqtarget_concipaths_Suc : 
   "ithpath succ s n \<noteq> [] \<and> validfinpath M s (concipaths succ s (Suc n)) s' \<Longrightarrow> ((\<lambda>s. laststate (succ s)) ^^ (Suc n)) s = s'"
  apply (simp only: concipaths_right validfinpathsplit)
proof-
  assume "ithpath succ s n \<noteq> [] \<and> (\<exists>s''. validfinpath M s (concipaths succ s n) s'' \<and> validfinpath M s'' (ithpath succ s n) s')"
  from this obtain s'' where "ithpath succ s n \<noteq> [] \<and> validfinpath M s'' (ithpath succ s n) s'" by auto
  thus "((\<lambda>s. laststate (succ s)) ^^ (Suc n)) s = s'" using source_ithpath_eqtarget_Suc by simp
qed

lemma validinfpathconc : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (\<exists>s' \<in> S'. validfinpath M s (succ s) s')) \<Longrightarrow> validinfpath M s (recursiveconcpaths succ s)"
  apply (simp add: validinfpath_def del: recursiveconcpaths.simps)
proof
  assume "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (\<exists>s' \<in> S'. validfinpath M s (succ s) s'))"
  hence assum1 : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> validfinpath M s (succ s) (laststate (succ s)) \<and> laststate (succ s) \<in> S')" using validfinpathlaststate by metis
  have "s = source ((succ s)!0)" using validfinpathsource assum1 by metis
  thus "s = source (recursiveconcpaths succ s 0)" using assum1 by simp
  have res1: "\<forall>n. \<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s'"
  proof
    fix n
    have "s \<in> S' \<longrightarrow> (\<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s')" by (induct n arbitrary: s; simp; metis assum1)
    thus "\<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s'" using assum1 by simp
  qed
  show "\<forall>n. recursiveconcpaths succ s n \<in> transition M \<and> target (recursiveconcpaths succ s n) = source (recursiveconcpaths succ s (Suc n))"
  proof
    fix n
    have allnonempty : "(\<forall>j<Suc (Suc n). ithpath succ s j \<noteq> [])" using allithpath_notempty assum1 by metis
    hence "Suc (Suc n) \<le> length (concipaths succ s (Suc (Suc n)))" by (simp only : lengthconcipaths)
    hence "n < length (concipaths succ s (Suc (Suc n))) \<and> Suc n < length (concipaths succ s (Suc (Suc n)))" by arith
    hence "(concipaths succ s (Suc (Suc n)))!n \<in> transition M \<and> target ((concipaths succ s (Suc (Suc n)))! n) = source ((concipaths succ s (Suc (Suc n)))!(Suc n))" using ithtransitionfinpath ithtargetsourcefinpath res1 by metis
    moreover have "Suc n < Suc (Suc n) \<and> n < Suc (Suc n)" by auto
    moreover from this allnonempty have "recursiveconcpaths succ s (Suc n) = (concipaths succ s (Suc (Suc n)))!(Suc n) \<and> recursiveconcpaths succ s n = (concipaths succ s (Suc (Suc n)))! n" by (simp only: concipaths_nth)
    ultimately show "recursiveconcpaths succ s n \<in> transition M \<and> target (recursiveconcpaths succ s n) = source (recursiveconcpaths succ s (Suc n))" by simp
  qed
qed

lemma successorlemma :
  assumes "(s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> P t \<and> t \<in> transition M \<and> target t \<in> S')))"
  shows "(\<exists> p. validinfpath M s p \<and> (\<forall>n. P (p n)))"
proof-
  from assms obtain succ where assum1: "\<forall>s'. s' \<in> S' \<longrightarrow> source (succ s') = s' \<and> P (succ s') \<and> (succ s') \<in> transition M \<and> target (succ s') \<in> S'" by metis
  let ?p = "recursiveconcpaths (\<lambda>s'. [succ s']) s"
  have "validinfpath M s ?p" by (rule validinfpathconc [where ?S'=S']; simp add: assum1 assms)
  moreover {
    fix n
    have "s \<in> S' \<longrightarrow> P (?p n)" by (induct n arbitrary: s; simp add: assum1)
  }
  ultimately have "validinfpath M s ?p \<and> (\<forall>n. P (?p n))" using assms by simp
  thus ?thesis by auto
qed

lemma successorlemma_no_pred : 
  assumes "s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> S'))"
  shows "\<exists> p. validinfpath M s p"
proof-
  from assms have assum1: "(s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> True \<and> t \<in> transition M \<and> target t \<in> S')))" by auto
  have "(\<exists> p. validinfpath M s p \<and> (\<forall>n. (\<lambda>t. True) (p n)))"
    apply (rule successorlemma)
    using assum1 apply (auto)
    done
  thus "(\<exists> p. validinfpath M s p)" by auto
qed

lemma exists_extensionpath :
  "(\<exists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}) \<or> (\<exists>p. validinfpath M s p)"
proof-
  have "(\<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}) \<Longrightarrow> (\<exists>p. validinfpath M s p)"
  proof-
    assume assum1: "\<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}"
    let ?S' = "{s. \<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}}"
    have res1: "s \<in> ?S'" using assum1 by auto
    have res2: "\<forall>s'. s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> ?S')" using assum1 invariantextension by auto
    show "\<exists> p. validinfpath M s p"
      apply (rule successorlemma_no_pred)
      using res1 res2 apply blast
      done
  qed
  thus ?thesis by auto
qed  

lemma extendpath :
  assumes "validfinpath M s p s'"
  shows "(\<exists>p' s''. validfinpath M s (p @ p') s'' \<and> enabledactions M s'' = {}) \<or> (\<exists>p'. validinfpath M s (conc p p'))"
proof-
  have "(\<exists>p' s''. validfinpath M s' p' s'' \<and> enabledactions M s'' = {}) \<or> (\<exists>p'. validinfpath M s' p')" using exists_extensionpath by metis 
  thus ?thesis using assms validinfpathsplit validfinpathsplit by metis
qed

lemma splitvalidfinpath_notoccurslockedenabled : "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)) =
  ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" 
  (is "?L = (?R1 \<or> ?R2 \<or> ?R3)")
proof
  {
    assume ?R2
    from this obtain p' s' i where assum1 : "i < length p' \<and> validfinpath M s p' s' \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e \<and> locked M B s'" by auto
    have "action (p'!i) \<in> \<alpha>\<^sub>e \<and> (source (p'!i), action (p'!i), target (p'!i)) \<in> transition M" using assum1 by auto
    hence "enabled M (source (p'!i)) \<alpha>\<^sub>e" by (simp add: enabled_def enabledactions_def; blast)
    moreover have "validfinpath M s (take i p') (source (p'!i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p')))" using assum1 by auto
    ultimately have ?L by auto   
  }
  moreover {
    assume ?R3
    from this obtain p' i where assum1 : "validinfpath M s p' \<and>  \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and>  action (p' i) \<in> \<alpha>\<^sub>e" by auto
    hence "p' i \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using validinfpath_def by metis
    hence "(source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" by simp
    hence "enabled M (source (p' i)) \<alpha>\<^sub>e" by (simp add: enabled_def enabledactions_def; blast)
    hence "validfinpath M s (prefix i p') (source (p' i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> enabled M (source (p' i)) \<alpha>\<^sub>e" using assum1 validinfsubpath by metis
    hence ?L by blast
  }
  ultimately show "(?R1 \<or> ?R2 \<or> ?R3) \<Longrightarrow> ?L" by blast
next
  assume ?L
  from this obtain p s' where "(validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by (auto simp : enabled_def enabledactions_def)
  moreover {
    assume "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M)"
    from this obtain s'' a where assum1 : "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M" by auto
    let ?t = "(s', a, s'')"
    have "validfinpath M s (p@[?t]) s''" using assum1 by simp
    hence "(\<exists>p' s''. validfinpath M s ((p@[?t]) @ p') s'' \<and> (enabledactions M s'' = {})) \<or> (\<exists>p'. validinfpath M s (conc (p@[?t]) p'))" by (rule extendpath)
    moreover {
      assume "\<exists>p' s''. validfinpath M s ((p@[?t]) @ p') s'' \<and> (enabledactions M s'' = {})"
      from this obtain p' s'' where "validfinpath M s ((p@[?t]) @ p') s'' \<and> locked M B s''" by (auto simp: locked_def)
      hence "validfinpath M s ((p@[?t]) @ p') s'' \<and> length p < length ((p@[?t]) @ p') \<and> \<not> occurs \<alpha>\<^sub>f (fin (take (length p) ((p@[?t]) @ p'))) \<and> action (((p@[?t]) @ p') ! (length p)) \<in> \<alpha>\<^sub>e \<and> locked M B s''" using assum1 by auto
      hence ?R2 by blast
    }
    moreover {
      assume "\<exists>p'. validinfpath M s (conc (p@[?t]) p')"
      from this obtain p' where "validinfpath M s (conc (p@[?t]) p')" by auto
      moreover have "prefix (length p) (conc (p@[?t]) p') = p" by (induct p; simp)
      moreover have "(conc (p@[?t]) p') (length p) = ?t" by (induct p; simp)
      ultimately have "validinfpath M s (conc (p@[?t]) p') \<and> \<not> occurs \<alpha>\<^sub>f (fin (prefix (length p) (conc (p@[?t]) p'))) \<and> action ((conc (p@[?t]) p') (length p)) \<in> \<alpha>\<^sub>e" using assum1 by auto
      hence ?R3 by blast
    }
    ultimately have "?R2 \<or> ?R3" by auto
  }
  ultimately show "?R1 \<or> ?R2 \<or> ?R3" by auto
qed

lemma freeuntiloccurrenceprogressing_lockedenabled: "(\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
  ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p)))"
  apply (subst existfreeuntiloccurrenceprogressing_cases)
  apply (subst splitvalidfinpath_notoccurslockedenabled)
  apply auto
  done

lemma progressingsubpath : "progressing M s B p \<Longrightarrow> (\<exists>s'. validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p))"
  apply (cases p; simp)
  apply (metis append_take_drop_id validfinpathsplit)
  apply (metis validinfsubpath validinfsubpathright)
  done

lemma splitviolating [simp] : "(\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) =
  (\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p')"
  (is "?L = ?R")
proof
  assume ?L
  from this obtain p i where "match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" using violating_def by blast
  hence "\<exists>s'. match \<rho> (pref i p) \<and> validfinpath M s (pref i p) s' \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B (suff i p)" by (simp add: progressingsubpath)
  thus ?R by auto
next
  assume ?R
  from this obtain p p' s' where assum1: "match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'" by auto
  {
    fix fp
    assume assum2 : "p' = fin fp"
    hence "match \<rho> p \<and> freeuntiloccurrence (fin fp) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 by auto
    hence "match \<rho> (pref (length p) (fin (p @ fp))) \<and> freeuntiloccurrence ((suff (length p) (fin (p @ fp)))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence "violating (fin (p @ fp)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating_def by metis
    moreover have "progressing M s B (fin (p @ fp))" using assum1 assum2 by auto
    ultimately have "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover {
    fix ip
    assume assum2 : "p' = inf ip"
    have "match \<rho> p \<and> freeuntiloccurrence (inf ip) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 assum2 by auto
    hence "match \<rho> (prefix (length p) (conc p ip)) \<and> freeuntiloccurrence (inf (suffix (length p) (conc p ip))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence "violating (inf (conc p ip)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating_def pref.simps suff.simps by blast
    moreover have "progressing M s B (inf (conc p ip))" using assum1 assum2 by auto
    ultimately have "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  ultimately show "?R \<Longrightarrow> ?L" by (cases p')
qed

lemma suffpredicate: 
  assumes invarfin: "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) = (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))) ))))"
  shows "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p \<longrightarrow> P s' (suff i p)"
  apply (cases p)
proof
  fix p'
  assume assum1: "p = fin p'"
  assume "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p"
  hence "validfinpath M s (take i p') s' \<and> (\<exists>s''. validfinpath M s' (drop i p') s'' \<and> locked M B s'') \<and> P s (fin p')" using assum1 by simp
  hence "progressing M s' B (fin (drop i p'))" by simp
  thus "P s' (suff i p)" using assum1 assms(1) by auto
next
  fix p'
  assume assum1: "p = inf p'"
  show "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p \<longrightarrow> P s' (suff i p)"
  proof
    assume "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p"
    hence valid : "validfinpath M s (prefix i p') s' \<and> validinfpath M s' (suffix i p') \<and> P s (inf p')" using assum1 by simp
    moreover have "conc (prefix i p') (suffix i p') = p'" by simp
    ultimately have "validinfpath M s p' \<and> P s (inf p')" using validinfpathsplit by metis
    hence assum2: "\<forall>a \<in> -B. ((\<forall>i. (source (p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' i)) (inf (suffix i p'))) ))" using invarinf by blast
    hence "\<forall>a \<in> -B. ((\<forall>l. (source ((suffix i p') l)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix l (suffix i p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source ((suffix i p') l)) (inf (suffix l (suffix i p'))) )))" by auto
    hence "P s' (inf (suffix i p'))" using invarinf valid by blast
    thus "P s' (suff i p)" using assum1 by auto
  qed
qed

end