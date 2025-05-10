(*                                                                                  *)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  This applies to all files in this archive except folder                         *)
(*  "system-semantics".                                                             *)
(*                                                                                  *)
(*  Copyright (c) 2023,                                                             *)
(*     Zongyuan Liu                                                                 *)
(*     Angus Hammond                                                                *)
(*     Jean Pichon-Pharabod                                                         *)
(*     Thibaut Pérami                                                               *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(*                                                                                  *)

From stdpp.bitvector Require Import definitions tactics.

From iris.proofmode Require Import tactics.

From self.low Require Import instantiation.
From self.low.lib Require Import edge event.
From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Section lemmas.
  Context `{AAIrisG}.

  Lemma rf_to_po eid eid' :
    EID.tid eid = EID.tid eid' ->
    eid -{Edge.Rf}> eid' -∗
    eid -{Edge.Po}> eid'.
  Proof.
    rewrite edge_eq.
    unfold edge_def.
    iIntros (tid_eq) "(%graph & (agree & %consistent & %wf & %edge_interp))".
    iExists graph.
    iFrame (consistent wf) "agree".
    iPureIntro.
    simpl in edge_interp |- *.
    apply Graph.wf_rfi_inv; assumption.
  Qed.

  Lemma loc_of_writes {gr ks kv ks' kv' a v v'} eid eid' :
    Event.event_interp gr (Event.W ks kv a v) eid ->
    Event.event_interp gr (Event.W ks' kv' a v') eid' ->
    (eid, eid') ∈ AACandExec.Candidate.loc gr.
  Proof.
    intros HE1 HE2.
    unfold Event.event_interp in *.
    clear -HE1 HE2.
    destruct HE1 as (E1 & HE1gr & HE1).
    destruct HE2 as (E2 & HE2gr & HE2).
    set_unfold.
    unfold AAConsistent.event_is_write_with, AAConsistent.event_is_write_with_P in HE1.
    exists E1, E2, a.
    split; [assumption|].
    split.
    {
      destruct E1. destruct o; try contradiction. rewrite CBool.bool_unfold in HE1. simpl.
      f_equal.
      destruct HE1 as (_ & _ & HE1).
      unfold AAConsistent.addr_and_value_of_wreq in HE1.
      destruct (decide (n = AAArch.val_size)); [| destruct t0; congruence].
      destruct t0. unfold eq_rec_r, eq_rec in HE1. subst. simpl. inversion HE1. reflexivity.
    }
    split; [assumption|].
    destruct E2. destruct o; try contradiction. rewrite CBool.bool_unfold in HE2. simpl.
    f_equal.
    destruct HE2 as (_ & _ & HE2).
    unfold AAConsistent.addr_and_value_of_wreq in HE2.
    destruct (decide (n = AAArch.val_size)); [| destruct t0; congruence].
    destruct t0. unfold eq_rec_r, eq_rec in HE2. subst. simpl. inversion HE2. reflexivity.
  Qed.

  Lemma po_to_co eid eid' addr :
    eid -{Edge.Po}> eid' -∗
    (∃ ks kv v, eid -{E}> (Event.W ks kv addr v)) -∗
    (∃ ks kv v, eid' -{E}> (Event.W ks kv addr v)) -∗
    eid -{Edge.Co}> eid'.
  Proof.
    rewrite event_eq /event_def. rewrite edge_eq /edge_def.
    iIntros "(%gr & Hgr1 & %Hgraph_co & % & %Hpo)
             (%ks & %kv & %v & % & Hgr2 & _ & _ & %HE1) (%ks' & %kv' & %v' & % & Hgr3 & _ & _ & %HE2)".
    iDestruct (graph_agree_agree with "Hgr2 Hgr1") as %->.
    iDestruct (graph_agree_agree with "Hgr3 Hgr1") as %->.
    iExists gr.
    iFrame "%∗".
    iPureIntro.
    unfold Edge.ef_edge_interp.
    apply Graph.wf_coi_inv; try assumption.
    + apply (loc_of_writes _ _ HE1 HE2).
    + assert (G : eid ∈ AACandExec.Candidate.mem_writes gr).
      {
        unfold Event.event_interp in HE1.
        destruct HE1 as (E1 & HE1gr & HE1).
        apply (AAConsistent.event_is_write_with_elem_of_mem_writes eid E1 ks kv addr v); assumption.
      }
      assert (G' : eid' ∈ AACandExec.Candidate.mem_writes gr).
      {
        unfold Event.event_interp in HE2.
        destruct HE2 as (E2 & HE2gr & HE2).
        apply (AAConsistent.event_is_write_with_elem_of_mem_writes eid' E2 ks' kv' addr v'); assumption.
      }
      set_solver + G G'.
  Qed.
End lemmas.

Section Proof.
  Context `{AAIrisG} (addr data : bv 64).

  Definition instrs : iProp Σ :=
    BV 64 4096 ↦ᵢ ILoad AS_normal AV_plain "r1" (AEval addr) ∗
    BV 64 4100 ↦ᵢ IStore AS_normal AV_plain "" (AEval data) (AEval addr) ∗
    BV 64 4104 ↦ᵢ -.

  Context (tid : Tid).

  Definition prot (v : Val) (e : Eid) : iProp Σ :=
    ⌜ EID.tid e = 0%nat ⌝ ∨ (⌜ v = data ⌝ ∗ ⌜ EID.tid e = tid ⌝).

  Context `{!AAThreadG} `{ThreadGN}.

  Lemma prog ctrl :
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write tid addr None -∗
    Prot[ addr | prot ] -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    instrs -∗
    WPi (LTSI.Normal, BV 64 4096) @ tid {{
      λ lts,
        ⌜ lts = (LTSI.Done, BV 64 4104) ⌝ ∗
        ∃ r w v, (* TODO: remove v *)
          r -{E}> Event.R AS_normal AV_plain addr v ∗
          w -{E}> Event.W AS_normal AV_plain addr data ∗
          r -{Edge.Fr}> w
    }}.
  Proof.
    iIntros "lpo ctrl rmw localw [prot1 prot2] [%rv1 r1] (#I1 & #I2 & #I3)".

    (* [1] ILoad AS_normal AV_plain "r1" (AEval addr) *)
    iApply sswpi_wpi.
    iApply (sswpi_mono with "[r1 lpo ctrl rmw localw prot1]").
    {
      iApply (iload_pln (flip prot) ∅ ∅ with "[$I1 $r1 $lpo $ctrl $rmw $localw]").
      {
        rewrite big_sepS_empty big_sepM_empty.
        iSplitL ""; iEmpIntro.
      }

      unfold flip.

      iIntros (r).
      iSplitL "";
        [iIntros "_ _"; rewrite big_sepM_empty; iEmpIntro | ].

      iExists _, _, emp%I.
      iSplitL "prot1";
        [iIntros "_"; iFrame "prot1" | ].

      iIntros (remote_w r_v) "_ _ _ _ _ _ _ #addr".
      iModIntro.
      iFrame "addr".
    }
    unfold flip.
    iIntros (?) "(
      -> & %r & %remote_w & %r_v & #r & %tid_r & r1 & own_r &
      (%remote_w_as & %remote_w_av & #remote_w) & #rf_r & lpo & _ & ctrl & rmw & localw
    )".
    assert ((BV 64 4096 `+Z` 4 = BV 64 4100)%bv) as G;
      [bv_solve | ].
    rewrite G.
    clear - tid_r.

    (* [2] IStore AS_normal AV_plain "" (AEval data) (AEval addr) *)
    iApply sswpi_wpi.
    iApply (sswpi_mono with "[lpo ctrl localw prot2]").
    {
      iDestruct (lpo_to_po with "lpo") as "[lpo #po]".
      iApply (istore_pln (prot data) {[r]} ∅ with "[$I2 $lpo $ctrl $localw]").
      {
        rewrite big_sepS_singleton big_sepM_empty.
        iFrame "po".
      }

      iExists _, _, emp%I.
      iSplitL "prot2";
        [iIntros "_"; iFrame "prot2" | ].

      iIntros (w).
      iSplitL "".
      {
        iIntros "_ _ _".
        rewrite big_sepM_empty.
        iEmpIntro.
      }
      iIntros "_ %tid_w _ _ _".
      iModIntro.
      unfold prot.
      iPureIntro.
      split;
        [right; split; [reflexivity | exact tid_w] | right; split; [reflexivity | exact tid_w]].
    }
    iIntros (?) "(-> & %w & #w & %tid_w & lpo & #po & localw & ctrl & own_w)".
    iEval (rewrite big_sepS_singleton) in "po".
    assert ((BV 64 4100 `+Z` 4 = BV 64 4104)%bv) as G;
      [bv_solve | ].
    rewrite G.
    clear - tid_r tid_w.

    iAssert (⌜ r ≠ w ⌝%I) as "%r_neq_w".
    {
      iIntros (->).
      iApply (po_irrefl with "po").
    }

    (* [3] - *)
    iApply sswpi_wpi.
    iApply (sswpi_mono _ _ _ (λ s, ⌜ s = (LTSI.Done, BV 64 4104) ⌝)%I).
    {
      iApply (idone with "[$I3]").
      iPureIntro.
      reflexivity.
    }
    iIntros (? ->).

    (* termination *)
    iApply wpi_terminated.
    iApply (
      inst_post_lifting_lifting
      _ _ _ {[w := prot data w; r := prot r_v remote_w]}
      with "[own_r own_w]"
    ).
    {
      set_solver.
    }
    {
      rewrite big_sepM_insert.
      {
        iFrame "own_w".
        iApply (big_sepM_singleton with "own_r").
      }
      rewrite lookup_singleton_None.
      exact r_neq_w.
    }
    iIntros "P".
    iModIntro.
    iSplitL "";
      [iPureIntro; reflexivity | ].
    iExists _, _, _.
    iFrame "r w".
    iApply (rf_co_to_fr with "rf_r").
    iPoseProof (big_sepM_insert with "P") as "(_ & P)";
      [rewrite lookup_singleton_None; exact r_neq_w | ].
    iPoseProof (big_sepM_insert with "P") as "(P & _)";
      [reflexivity | ].
    unfold prot.
    iDestruct "P" as "[%tid_remote_w | (<- & %tid_remote_w)]".
    {
      iApply (initial_write_co _ _ _ _ _ _ _ _ _ tid_remote_w with "remote_w w").
      rewrite tid_w.
      lia.
    }
    iApply (po_to_co remote_w w addr with "[] [$remote_w] [$w]").
    iApply (po_trans with "[] po").
    iApply (rf_to_po with "rf_r").
    rewrite tid_r tid_remote_w.
    reflexivity.
  Qed.
End Proof.
