Require Import Setoid Omega RelationClasses Morphisms.

Require Export Bool Omega List Setoid Morphisms.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.

Instance le_preorder : PreOrder le.
Proof.
  constructor. all:cbv. all:intros;omega. 
Qed.

Instance S_le_proper : Proper (le ==> le) S.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance plus_le_proper : Proper (le ==> le ==> le) plus.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance mult_le_proper : Proper (le ==> le ==> le) mult.
Proof.
  cbv. intros. 
  apply mult_le_compat. all:eauto. 
Qed.


Instance max_le_proper : Proper (le ==> le ==> le) max.
repeat intro. repeat eapply Nat.max_case_strong;omega.
Qed.

Instance min_le_proper : Proper (le ==> le ==> le) min.
repeat intro. repeat eapply Nat.min_case_strong;omega.
Qed.

Instance Nat_log2_le_Proper : Proper (le ==> le) Nat.log2.
Proof.
  repeat intro. apply Nat.log2_le_mono. assumption.
Qed.
Instance Pos_to_nat_le_Proper : Proper (Pos.le ==> le) Pos.to_nat.
Proof.
  repeat intro. apply Pos2Nat.inj_le. assumption.
Qed.

Instance Pos_add_le_Proper : Proper (Pos.le ==> Pos.le ==>Pos.le) Pos.add.
Proof.
  repeat intro. eapply Pos.add_le_mono. 3:eauto. all:eauto. 
Qed.
