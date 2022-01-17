theory Common
  imports Main "HOL-Library.While_Combinator"
begin

(* A feasible set is a nonempty subset *)
abbreviation NonEmptySubset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "NonEmptySubset A U \<equiv> (A \<subseteq> U \<and> A \<noteq> {})"

(* 
  What follows is a lemma to show that if a property is true for some finite set, and we can always
  find a nonempty strict subset that also has the property, then, after repeated application, we
  will eventually end up with a singleton subset of the original set, that also has the property.
*)

abbreviation filled where "filled \<equiv> \<lambda>G. finite G \<and> G \<noteq> {}"

context
  fixes G :: "'a set"
    and P :: "'a set \<Rightarrow> bool"
  assumes filled_G: "filled G"
      and initial: "P G"
begin

lemma sub_finite: "G' \<subseteq> G \<Longrightarrow> finite G'" using filled_G by (metis finite_subset) 

abbreviation P' where "P' G' \<equiv> P G' \<and> G' \<sqsubseteq> G"
abbreviation C where "C G' \<equiv> P' G' \<and> card G' \<noteq> 1"

abbreviation Q where "Q s G' \<equiv> P' G' \<and> G' \<subset> s"
abbreviation S where "S s \<equiv> SOME G'. Q s G'"

lemma subset_descent:
  assumes step: "\<And>s. C s \<Longrightarrow> \<exists>G'. Q s G'"
  shows "\<exists>g \<in> G. while C S G = {g} \<and> P {g}"
proof (rule while_rule[where P = P' and r = finite_psubset])
  show "P' G" using filled_G initial by simp next
  show "P' s \<Longrightarrow> C s \<Longrightarrow> P' (S s)" for s using someI2_ex[of "Q s" "\<lambda>G'. G' \<subseteq> G"] someI2_ex[of "Q s" P] someI2_ex[of "Q s" filled] step sub_finite by simp
next
  show "P' s \<Longrightarrow> \<not> C s \<Longrightarrow> \<exists>g \<in> G. s = {g} \<and> P {g}" for s proof -
    assume "P' s" "\<not> C s"
    hence "s \<subseteq> G" "P s" "card s = 1" by auto
    then obtain g where "g \<in> G \<and> s = {g} \<and> P {g}" by (metis card_1_singletonE in_mono singletonI) 
    thus ?thesis by auto
  qed next
  show "wf finite_psubset" using wf_finite_psubset . next
  show "P' s \<Longrightarrow> C s \<Longrightarrow> (S s, s) \<in> finite_psubset" for s using someI2_ex[of "Q s" "\<lambda>G. G \<subset> s"] step sub_finite by auto
qed

end

end