theory paths
imports syntaxsemantics "HOL-Library.Omega_Words_Fun"
begin

type_synonym ('a, 's) finpath = "('s \<times> 'a \<times> 's) list"
type_synonym ('a, 's) infpath = "('s \<times> 'a \<times> 's) word"

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

lemma split [simp] : "(source t, action t, target t) = t"
  by (simp add: source_def action_def target_def)

fun validfinpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's \<Rightarrow> bool" where
"validfinpath M s [] s' = (s = s')" |
"validfinpath M s (t#ts) s' = (s = source t  \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (source (p 0) = s \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

definition enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

fun progressing :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M s B (fin p) = (\<exists>s'. validfinpath M s p s' \<and> locked M B s')" |
"progressing M s B (inf p) = validinfpath M s p"

definition match :: "'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> regformtolanguage \<rho>)"

fun matchntimes :: "nat \<Rightarrow> 'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"matchntimes 0 R p = (p = [])" |
"matchntimes (Suc n) R p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')"

lemma existmatchntimessplit : "(\<exists>p' p''. p = p'@p'' \<and>  match R p' \<and> matchntimes n R p'') = (matchntimes (Suc n) R p)"
  apply (induct n; simp)
  done

lemma existsninduct [simp] : "((\<exists>n. P (Suc n)) \<or> P 0) = (\<exists>n. P n)"
  using zero_induct by blast

lemma matchrepeat_eq_matchntimes : "match (repeat R) (p :: ('a, 's) finpath) = (\<exists>n. matchntimes n R p)"
proof-
  have "match (repeat R) (p :: ('a, 's) finpath) = (map action p \<in> (\<Union>n. (regformtolanguage R) ^^ n))" by (simp add: match_def)
  moreover have "... = (\<exists>n. map action (p :: ('a, 's) finpath) \<in> (regformtolanguage R) ^^ n)" by auto
  moreover have "\<forall>n. (map action (p :: ('a, 's) finpath) \<in> (regformtolanguage R) ^^ n) = (matchntimes n R p)"
  proof
    fix n
    show "(map action (p :: ('a, 's) finpath) \<in> (regformtolanguage R) ^^ n) = (matchntimes n R p)"
    apply (induct n arbitrary : p; simp)
  proof-
    fix n
    fix p :: "('a, 's) finpath"
    assume assum1 : "(\<And>(p :: ('a, 's) finpath). (map action p \<in> regformtolanguage R ^^ n) = matchntimes n R p)"
    have "(map action p \<in> regformtolanguage R @@ regformtolanguage R ^^ n) = (\<exists>p' p''. map action p = p' @ p'' \<and>  (p' \<in> regformtolanguage R) \<and> (p'' \<in> regformtolanguage R ^^ n))" by (rule conclem')
    moreover have "... = (\<exists>p' p''. p = p'@p'' \<and>  ((map action p') \<in> regformtolanguage R) \<and> ((map action p'') \<in> regformtolanguage R ^^ n))" by sorry
    moreover have "... = (\<exists>p' p''. p = p'@p'' \<and>  match R p' \<and>  matchntimes n R p'')" using assum1 by (auto simp: match_def) 
    ultimately show "(map action p \<in> regformtolanguage R @@ regformtolanguage R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')" by simp
  qed
  qed
  ultimately show "match (repeat R) (p :: ('a, 's) finpath) = (\<exists>n. matchntimes n R p)" by blast
qed

lemma matchunfold [simp] : 
  shows "match eps p = (p = [])"
  and "match (acts A) p = (\<exists>t. p = [t] \<and> action t \<in> A)"
  and "match (after R Q) p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> match Q p'')"
  and "match (union R Q) p = (match R p \<or> match Q p)"
  and "match (repeat R) p = (\<exists>n. matchntimes n R p)"
  prefer 5
  apply (rule matchrepeat_eq_matchntimes)
  apply (simp_all add: match_def)
  apply (rule iffI; auto)
  apply (rule iffI; metis append_eq_map_conv)
  done

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where 
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

lemma prefixleft : "(prefix (Suc n) p) = (p 0)#(prefix n (suffix (Suc 0) p))"
  by (induct n; simp)

lemma validfinpathsplit [simp] : "(\<exists>s''. validfinpath M s p s'' \<and> validfinpath M s'' p' s') = validfinpath M s (p @ p') s'"
  by (induct p arbitrary: s; simp)

lemma validfinsubpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M s (take (Suc i) p) (target (p!i))"
  apply (induct p arbitrary: s i)
  apply (simp)
proof-
  case Cons
  then show ?case by (cases i) auto
qed
 
lemma validinfsubpath : "validinfpath M s p \<Longrightarrow> (validfinpath M s (prefix i p) (source (p i)))"
  apply (induct i arbitrary : s p; simp add: validinfpath_def)
  apply (metis validfinpath.simps validfinpathsplit)
  done

fun occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A (fin p) = (\<exists> a \<in> A. a \<in> (set (map action p)))" |
"occurs A (inf p) = (\<exists> n. (action (p n)) \<in> A)" 

fun freeuntiloccurence :: "('a, 's) path \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e = ((\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (pref i p))) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)
  \<or> \<not>(occurs \<alpha>\<^sub>f p))"

fun violating :: "('a, 's) path \<Rightarrow> 'a regularformula \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. match \<rho> (pref i p) \<and> freeuntiloccurence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)"

lemma emptylist [simp] : "(pref i p = []) = (i = 0 \<or> p = fin [])"
  using take_eq_Nil by (cases p) simp_all

lemma emptypath : "p = [] \<and> validfinpath M s p s' \<Longrightarrow> (s' = s)"
  by (induct p; simp)

lemma nosuffix : "(p = fin [] \<or> i = 0) \<Longrightarrow> (suff i p = p)"
  by (cases p) auto

lemma violatingempty [iff] : "violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e = freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e"
proof-
  have "violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. (pref i p) = [] \<and> freeuntiloccurence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by (simp add : match_def)
  moreover have "... = (\<exists>i. (i = 0 \<or> p = fin []) \<and> freeuntiloccurence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by auto
  moreover have "... = (freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e)" using nosuffix by metis
  ultimately show ?thesis by auto
qed

lemma unfoldcasesinf :
  assumes "freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p"
  and "p = inf infpath"
  shows "\<not>(occurs \<alpha>\<^sub>f p) \<or> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (pref i p))) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)"
  using assms by auto

lemma unfoldcases [simp] : "(\<exists> p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
 ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
proof
  assume "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p"
  from this obtain p where assum1 : "freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by auto
  have "(freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = ((\<exists>p' s'. p = fin p' \<and>  validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'.  p = fin p' \<and> validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. p = inf p' \<and>  validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. p = inf p' \<and> validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
    apply (cases p)
    apply auto[1]
    apply auto[1]
    done
  thus "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" using assum1 by blast 
next
  assume "(\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
    (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
    (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
    (\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))"
  moreover { 
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'"
    from this obtain p' where "\<exists>s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'" by auto
    hence "freeuntiloccurence (fin p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin p')" by auto 
    hence "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'"
    from this obtain p' where "\<exists>s'. validfinpath M s p' s' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'" by auto
    hence "freeuntiloccurence (fin p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin p')" by auto 
    hence "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')"
    from this obtain p' where "validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')" by auto
    hence "freeuntiloccurence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf p')" by auto 
    hence "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e)"
    from this obtain p' where "validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e)" by auto
    hence "freeuntiloccurence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf p')" by auto 
    hence "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  ultimately show "\<exists>p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
qed

(*this is hardest*)
lemma splitvalidfinpathnotoccurslockedenabled : "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
= ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" 
  apply (rule iffI)
proof-
  assume "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
  moreover {
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'"
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by auto
  }
  moreover {
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'"
    from this obtain p' s' i where "validfinpath M s p' s' \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'" by auto
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by aut
  }
  moreover {
    assume "\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)"
    from this obtain p' i where assum1 : "validinfpath M s p' \<and>  \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and>  action (p' i) \<in> \<alpha>\<^sub>e" by auto
    hence "p' i \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using validinfpath_def by metis
    hence "(source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" by simp
    hence "validfinpath M s (prefix i p') (source (p' i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> (source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using assum1 validinfsubpath assum1 by metis
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M)" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M))" by blast
next
  assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))"
  show "(\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') 
  \<or> (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') 
  \<or> (\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))" by sorry
qed

lemma splitcases [simp]: "(\<exists> p. freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p))"
  apply (subst unfoldcases)
  apply (subst splitvalidfinpathnotoccurslockedenabled)
  apply (auto)
  done

lemma splitviolating [simp] : "(\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
  (\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> violating p' eps \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p')"
proof- 
  show "(\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
  (\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> violating p' eps \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p')" by sorry
qed

lemma violatingprogressingcases : "(\<exists>p. violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
 (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p))"
proof-
  show "(\<exists>p. violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
 (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p))" by sorry
qed

end