From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export lang proofmode.
From diaframe.heap_lang Require Import proof_automation.
From diaframe.lib Require Import atomic.
From diaframe.symb_exec Require Import atom_spec_notation.
From eactris.utils Require Import queue.

Definition new_chan : val :=
  λ: <>,
    let: "l" := new_queue #() in
    let: "r" := new_queue #() in
    ((Fst "l", Snd "r"), (Fst "r", Snd "l")).

Definition send : val :=
  λ: "c" "m" "drop",
  let: "l" := Fst "c" in
  enqueue "l" "m" "drop".

Definition recv : val :=
  λ: "c",
  let: "r" := Snd "c" in
  dequeue "r".

Definition cancel : val :=
  λ: "c",
  let: "l" := Fst "c" in
  let: "r" := Snd "c" in
  cancel_back "l";;
  cancel_front "r".

Definition flip_qstate s :=
  {| active_front := active_back s; active_back := active_front s |}.

Definition is_chan_def `{!heapGS Σ, !queueG Σ}
  (c c' : val) (s : QueueState) (q q' : list (val * val)) : iProp Σ :=
  ∃ (e d e' d' : loc),
    ⌜ c = (#e,#d')%V ⌝ ∗ ⌜ c' = (#e',#d)%V ⌝ ∗
    is_queue s e d q ∗ is_queue (flip_qstate s) e' d' q'.

Local Definition is_chan_aux : seal (@is_chan_def). Proof. by eexists. Qed.
Definition is_chan := is_chan_aux.(unseal).
Local Definition is_chan_unseal :
  @is_chan = @is_chan_def := is_chan_aux.(seal_eq).
Global Arguments is_chan {Σ _ _} c c' s q q'.

Global Instance is_chan_timeless `{!heapGS Σ, !queueG Σ} c c' s q q' :
  Timeless (is_chan c c' s q q').
Proof. rewrite is_chan_unseal. by apply _. Qed.

Definition chan_handle_def `{!heapGS Σ, !queueG Σ} (c : val) : iProp Σ :=
  ∃ (e d : loc), ⌜c = (#e, #d)%V⌝ ∗
    enqueue_handle e ∗ dequeue_handle d.

Local Definition chan_handle_aux : seal (@chan_handle_def). Proof. by eexists. Qed.
Definition chan_handle := chan_handle_aux.(unseal).
Local Definition chan_handle_unseal :
  @chan_handle = @chan_handle_def := chan_handle_aux.(seal_eq).
Global Arguments chan_handle {Σ _ _} c.

Section lemmas.

  Context `{heapGS Σ, queueG Σ}.

  Global Instance flip_qstate_involutive : (Involutive eq flip_qstate).
  Proof. by case. Qed.

  Lemma is_chan_sym c c' s q q' :
    is_chan c c' s q q' -∗
    is_chan c' c (flip_qstate s) q' q.
  Proof.
    rewrite is_chan_unseal. iSteps. by rewrite flip_qstate_involutive.
  Qed.

End lemmas.

Section specs.

  Context `{heapGS Σ, queueG Σ}.

  Set Default Proof Using "Type".

  Global Instance new_chan_spec :
    SPEC {{ True }}
      new_chan #()
    {{ c c', RET (c, c')%V;
      let starting_state := {| active_front := true; active_back := true |} in
      is_chan c c' starting_state [] [] ∗ chan_handle c ∗ chan_handle c' ∗ £ 4 }}.
  Proof.
    rewrite is_chan_unseal chan_handle_unseal. by iSteps.
  Qed.

  Global Instance send_spec (c m drop : val) :
    SPEC ⟨ ↑N ⟩ c' s q q' P n,
    << chan_handle c ¦ is_chan c c' s q q' ∗
      (if active_front s then emp else (P ∧ drop_spec drop)) ∗ steps_lb n >>
      send c m drop
    << RET #(); chan_handle c ¦
       is_chan c c' s (q ++ [(m, drop)]) q' ∗ steps_lb (S n) ∗ £ (4 + n) >>.
  Proof.
    rewrite is_chan_unseal chan_handle_unseal.
    iStep 31 as (e d Φ) "d AU £".
    iMod "AU" as (c' s q q' P n) "(((% & %d' & %e' & % & %h & -> & queue & queue') & drop & steps) & close)".
    move: h=>[<-<-]. clear.
    iExists s, d', P, q, n. iStep 4 as "steps _ drop queue" / as "_ steps queue £".
    + iDestruct "close" as "(repeat & _)".
      by iMod ("repeat" with "[queue queue' drop]"); iSteps.
    + iDestruct "close" as "(_ & close)".
      by iMod ("close" with "[queue queue' £]"); iSteps.
  Qed.

  Global Instance recv_spec c :
    SPEC ⟨ ↑N ⟩ c' s q q',
    << chan_handle c ¦ is_chan c c' s q q' >>
      recv c
    << (om : val), RET om; chan_handle c ¦
      match q' with
      | [] => ⌜om = NONEV⌝ ∗ ⌜active_front s = false⌝ ∗ is_chan c c' s q []
      | (m, _) :: q' => ⌜om = SOMEV m⌝ ∗ is_chan c c' s q q'
      end ∗ £ 3 >>.
  Proof.
    rewrite is_chan_unseal chan_handle_unseal.
    iSteps as (e d Φ) "e AU £".
    iMod "AU" as (c' s q q') "((% & %d' & %e' & % & %h & -> & queue & queue') & close)".
    move: h=>[<-<-]. clear.
    iStep 4 as "queue'" / as (om) "queue'".
    + iDestruct "close" as "(repeat & _)".
      by iMod ("repeat" with "[queue queue']") as "AU"; iSteps.
    + iDestruct "close" as "(_ & close)".
      iMod ("close" with "[queue queue' £]") as "Φ"; last by iSteps.
      case: q'=>[|[m _] q'].
      - iDecompose "queue'". by iSteps.
      - iDecompose "queue'". by iSteps.
  Qed.

  Global Instance cancel_spec c :
    SPEC ⟨ ↑N ⟩ c' s q q' P Q,
    << chan_handle c ¦ is_chan c c' s q q' ∗
      P ∗ (P ={∅}=∗ Q ∗ [∗ list] '(_, drop) ∈ q', drop_spec drop) >>
      cancel c
    << RET #(); is_chan c c' {| active_back := false; active_front := active_front s |} q [] ∗ Q >>.
  Proof.
    rewrite is_chan_unseal chan_handle_unseal.
    iStep 14 as (e d Φ) "e d AU (£1 & _)".
    iModIntro. wp_bind (Snd _).
    iMod (cancel_dequeue with "d") as "close_inv"; first done.
    iMod "AU" as (c' s q q' P Q) "(((% & %d' & %e' & % & %h & -> & queue & queue') & P & drops) & (_ & close))".
    move: h=>[<-<-]. clear.
    iDestruct (cancel_enqueue with "e queue") as "(e & queue)".
    iStep 4. iIntros "!>!>". iMod ("drops" with "P") as "(Q & drops)".
    iMod ("close_inv" with "queue' drops") as "(queue' & close_inv)".
    iMod ("close" with "[queue queue' Q]") as "Φ"; first by iSteps. iModIntro.
    iMod "close_inv" as "d".
    by iSteps.
  Qed.

End specs.