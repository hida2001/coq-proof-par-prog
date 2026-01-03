(* Example: Parallel Program Verification *)
From iris.algebra Require Import auth list excl gset numbers csum.
From iris.algebra Require Export ofe.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import par lang proofmode notation.

Section proof.

Context `{!heapGS Σ, spawnG Σ, !inG Σ (prodR (gset_disjR bool) (optionR (exclR unitO)))}.

(* function for acquiring a lock *)
Definition acquire : expr :=
  rec: "acquire" "l" :=
  if: CAS "l" #false #true then #() else "acquire" "l".

(* function for releasing a lock *)
Definition release : expr :=
  λ: "l", "l" <- #false.

(* program whose specification we want to prove *)
Definition prog (x:loc) : expr :=
  let: "lock" := ref #false in
          (acquire "lock";; #x <- #2 * ! #x ;; release "lock") |||
          (acquire "lock";; #x <- ! #x + #1 ;; release "lock").

Let N :=nroot .@ "lock".

Lemma prog_spec (x:loc) : {{{ x ↦ #2 }}} prog x {{{ (v:val), RET v; x ↦ #5 ∨ x ↦ #6 }}}.
Proof.
rewrite/prog.
iIntros (Φ) "Hmap HΦ".
wp_alloc lock as "Hlock".
wp_pures.
iMod (own_alloc ((GSet {[true]} ⋅ GSet {[false]}) ⋅ GSet ∅, (None ⋅ None) ⋅ (Some (Excl(()))))) as "[%γ Hown]". { done. }
rewrite pair_op own_op.
iDestruct "Hown" as "[Hown H]".
rewrite pair_op own_op.
iDestruct "Hown" as "[Hownl Hownr]".
iMod (inv_alloc N _ ((lock ↦ #true) ∨ (lock ↦ #false ∗
                        ((x ↦ #2 ∗ own γ (GSet ∅, Some (Excl ())) ∨
                         (x ↦ #3 ∗ own γ (GSet {[false]}, None)) ∨
                         (x ↦ #4 ∗ own γ (GSet {[true]}, None)) ∨
                         (own γ (GSet {[true; false]}, None)))))) with "[Hlock Hmap H] ") as "#I".
{ iNext. iRight. iFrame. iLeft. iFrame. }
remember (λ _:val, (own γ (GSet ∅, Some (Excl ())) ∨ x ↦ #6))%I as Ψl.
remember (λ _:val, (own γ (GSet ∅, Some (Excl ())) ∨ x ↦ #5))%I as Ψr.
wp_apply (wp_par Ψl Ψr with "[Hownl] [Hownr] ").
{ wp_pures. iLöb as "IH".
  wp_bind (CmpXchg #lock #false #true).
  iInv "I" as "[Hlock|[Hlock [[H2 How]|[[H3 How]|[[H4 How]| How]]]]]".
  { wp_cmpxchg_fail. iModIntro. iSplitL "Hlock".
    { iNext. by iLeft. }
    wp_pures. by iApply "IH". }
  { wp_cmpxchg_suc.
    iCombine "Hownl How" as "Hown".
    rewrite op_None_left_id.
    iModIntro. iSplitL "Hlock".
    { by iLeft. }
    wp_pures. wp_load. wp_pures. wp_store. replace (2*2)%Z with 4%Z by lia.
    wp_pures.
    iInv "I" as "[Hlock'|[Hlock' [[H2' How']|[[H3' How']|[[H4' How']| How']]]]]";
    try solve [wp_store; iCombine "Hown How'" as "contra";
               iPoseProof (own_valid with "contra") as "%contra";
               by move:contra=>/pair_valid []].
    { wp_store.
      replace (Excl' ()) with (None ⋅ Excl' ()) at 2; last first.
      { by rewrite op_None_left_id. }
      rewrite pair_op own_op.
      iDestruct "Hown" as "[Hinv Hmid]".
      iModIntro. iSplitR "Hmid".
      { iNext. iRight. iFrame. iRight. iRight. iLeft. iFrame. }
      subst Ψl. by iLeft. }
    { wp_store.
      iAssert (⌜x ≠ x⌝)%I with "[H2 H3']" as %H0.
      { iApply (mapsto_frac_ne with "[H2] [H3']"); auto.
        rewrite dfrac_op_own. move=>/dfrac_valid_own.
        apply Qp.not_add_le_r. }
      done. }}
  { wp_cmpxchg_suc.
    iCombine "Hownl How" as "Hown".
    rewrite gset_disj_union; [| by apply disjoint_singleton_l]. 
    iModIntro. iSplitL "Hlock".
    { by iLeft. }
    wp_pures. wp_load. wp_pures. wp_store. replace (2*3)%Z with 6%Z by lia.
    wp_pures.
    iInv "I" as "[Hlock'|[Hlock' [[H2' How']|[[H3' How']|[[H4' How']| How']]]]]";
    try solve [wp_store; iCombine "Hown How'" as "contra";
               iPoseProof (own_valid with "contra") as "%contra";
               by move:contra=>/pair_valid []].
    { wp_store. iModIntro. iSplitR "H3".
      { iNext. iRight. iFrame. }
      subst Ψl. by iRight. }
    { wp_store.
      iAssert (⌜x ≠ x⌝)%I with "[H3 H2']" as %H0.
      { iApply (mapsto_frac_ne with "[H3] [H2']"); auto.
        rewrite dfrac_op_own. move=>/dfrac_valid_own.
        apply Qp.not_add_le_r. }
      done. }}
  { wp_cmpxchg_suc.
    iCombine "Hownl How" as "contra".
    iPoseProof (own_valid with "contra") as "%contra".
    move:contra=>/pair_valid [] /gset_disj_valid_op/elem_of_disjoint H0.
    exfalso. by apply H0 with true. }
  { wp_cmpxchg_suc.
    iCombine "Hownl How" as "contra".
    iPoseProof (own_valid with "contra") as "%contra".
    move:contra=>/pair_valid [] /gset_disj_valid_op/elem_of_disjoint H0.
    exfalso. by apply H0 with true. }}
{ wp_pures. iLöb as "IH".
  wp_bind (CmpXchg #lock #false #true).
  iInv "I" as "[Hlock|[Hlock [[H2 How]|[[H3 How]|[[H4 How]| How]]]]]".
  { wp_cmpxchg_fail. iModIntro. iSplitL "Hlock".
    { iNext. by iLeft. }
    wp_pures. by iApply "IH". }
  { wp_cmpxchg_suc.
    iCombine "Hownr How" as "Hown".
    rewrite op_None_left_id.
    iModIntro. iSplitL "Hlock".
    { by iLeft. }
    wp_pures. wp_load. wp_pures. wp_store. replace (2+1)%Z with 3%Z by lia.
    wp_pures.
    iInv "I" as "[Hlock'|[Hlock' [[H2' How']|[[H3' How']|[[H4' How']| How']]]]]";
    try solve [wp_store; iCombine "Hown How'" as "contra";
               iPoseProof (own_valid with "contra") as "%contra";
               by move:contra=>/pair_valid []].
    { wp_store.
      replace (Excl' ()) with (None ⋅ Excl' ()) at 2; last first.
      { by rewrite op_None_left_id. }
      rewrite pair_op own_op.
      iDestruct "Hown" as "[Hinv Hmid]".
      iModIntro. iSplitR "Hmid".
      { iNext. iRight. iFrame. iRight. iLeft. iFrame. }
      subst Ψr. by iLeft. }
  { wp_store.
    iAssert (⌜x ≠ x⌝)%I with "[H2 H4']" as %H0.
    { iApply (mapsto_frac_ne with "[H2] [H4']"); auto.
      rewrite dfrac_op_own. move=>/dfrac_valid_own.
      apply Qp.not_add_le_r. }
    done. }}
  { wp_cmpxchg_suc.
    iCombine "Hownr How" as "contra".
    iPoseProof (own_valid with "contra") as "%contra".
    move:contra=>/pair_valid [] /gset_disj_valid_op/elem_of_disjoint H0.
    exfalso. by apply H0 with false. }
  { wp_cmpxchg_suc.
    iCombine "Hownr How" as "Hown".
    rewrite cmra_comm gset_disj_union; [| by apply disjoint_singleton_l]. 
    iModIntro. iSplitL "Hlock".
    { by iLeft. }
    wp_pures. wp_load. wp_pures. wp_store. replace (4+1)%Z with 5%Z by lia.
    wp_pures.
    iInv "I" as "[Hlock'|[Hlock' [[H2' How']|[[H3' How']|[[H4' How']| How']]]]]";
    try solve [wp_store; iCombine "Hown How'" as "contra";
               iPoseProof (own_valid with "contra") as "%contra";
               by move:contra=>/pair_valid []].
    { wp_store. iModIntro. iSplitR "H4".
      { iNext. iRight. iFrame. }
      subst Ψr. by iRight. }
  { wp_store.
    iAssert (⌜x ≠ x⌝)%I with "[H4 H2']" as %H0.
    { iApply (mapsto_frac_ne with "[H4] [H2']"); auto.
      rewrite dfrac_op_own. move=>/dfrac_valid_own.
      apply Qp.not_add_le_r. }
    done. }}
  { wp_cmpxchg_suc.
    iCombine "Hownr How" as "contra".
    iPoseProof (own_valid with "contra") as "%contra".
    move:contra=>/pair_valid [] /gset_disj_valid_op/elem_of_disjoint H0.
    exfalso. by apply H0 with false. }}
subst Ψl Ψr.
iIntros (v1 v2) "[[Hownl|H6] [Hownr|H5]]".
{ iCombine "Hownl Hownr" as "Hown".
  iPoseProof (own_valid with "Hown") as "%contra".
  by move:contra=>/pair_valid []. }
{ iApply "HΦ". by iLeft. }
{ iApply "HΦ". by iRight. }
{ iAssert (⌜x ≠ x⌝)%I with "[H5 H6]" as %H0.
  { iApply (mapsto_frac_ne with "[H5] [H6]"); auto.
    rewrite dfrac_op_own. move=>/dfrac_valid_own.
    apply Qp.not_add_le_r. }
  done. }
Qed.
End proof.