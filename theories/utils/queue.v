From iris.base_logic.lib Require Import token.
From eactris.utils Require Import ghost_var.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export lang proofmode.
From iris.heap_lang Require Import array.
From diaframe.heap_lang Require Import proof_automation wp_later_credits.
From diaframe.lib Require Import atomic later_credits.
From diaframe.symb_exec Require Import atom_spec_notation.

Local Definition cancelled : val := #0.

Local Definition nil : val := #1.

Local Definition cons : val := #2.

Local Definition qnil : val :=
  λ: <>,
  let: "back" := AllocN #4 #() in
  "back" <- nil;;
  "back".

Definition new_queue : val :=
  λ: <>,
  let: "back" := qnil #() in
  (ref "back", ref "back").

Definition enqueue : val :=
  λ: "e" "m" "drop",
  let: "back" := qnil #() in
  let: "node" := !"e" in
  ("node" +ₗ #1) <- "m";;
  ("node" +ₗ #2) <- "drop";;
  ("node" +ₗ #3) <- "back";;
  if: CAS "node" nil cons then "e" <- "back" else
  "drop" #();;
  array_free "back" #4.

Definition dequeue : val :=
  rec: "dequeue" "d" :=
  let: "front" := !"d" in
  let: "i" := !"front" in
  if: "i" = nil then "dequeue" "d" else
  if: "i" = cancelled then NONE else
  let: "next" := !("front" +ₗ #3) in
  "d" <- "next";;
  let: "m" := !("front" +ₗ #1) in
  array_free "front" #4;;
  SOME "m".

Definition cancel_back : val :=
  λ: "e",
  let: "back" := !"e" in
  Free "e";;
  if: CAS "back" nil cancelled then #() else array_free "back" #4.

Definition cancel_front : val :=
  rec: "cancel" "d" :=
  let: "front" := !"d" in
  let: "i" := Fst (CmpXchg "front" nil cancelled) in
  if: "i" = cons then
    let: "m" := !("front" +ₗ #1) in
    let: "drop" := !("front" +ₗ #2) in
    let: "next" := !("front" +ₗ #3) in
    "d" <- "next";;
    "drop" #();;
    array_free "front" #4;;
    "cancel" "d"
  else
    Free "d";;
    if: "i" = nil then #() else array_free "front" #4.

Record QueueState := { active_back : bool; active_front : bool }.
Global Instance QueueState_Inhabited : Inhabited QueueState.
Proof. exists. apply {| active_back := true; active_front := true |}. Qed.

Class queueG Σ :=
    { #[local] queueG_enqueue_inG :: ghost_varG Σ bool;
      #[local] queueG_dequeue_inG :: ghost_varG Σ (bool * bool);
      #[local] queueG_queueG :: ghost_varG Σ (list (val * val));
      #[local] queueG_frontG :: ghost_varG Σ loc;
      #[local] queueG_tokenG :: tokenG Σ }.
Definition queueΣ : gFunctors :=
    #[ghost_varΣ bool; ghost_varΣ (bool * bool); ghost_varΣ (list (val * val)); ghost_varΣ loc; tokenΣ ].
Global Instance subG_queueΣ Σ : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.

Definition drop_spec_def `{heapGS Σ} (drop : val) : iProp Σ :=
  ∃ (P Q : iProp Σ) E,
  <<{ P }>> drop #() @E <<{ ∃∃ v, Q | RET v; True }>> ∗ AU <{ P }> @ ⊤ ∖ E, ∅ <{ Q, COMM True }>.

Local Definition drop_spec_aux : seal (@drop_spec_def). Proof. by eexists. Qed.
Definition drop_spec := drop_spec_aux.(unseal).
Local Definition drop_spec_unseal :
  @drop_spec = @drop_spec_def := drop_spec_aux.(seal_eq).
Global Arguments drop_spec {Σ _} drop.

Local Fixpoint is_queue_list `{heapGS Σ, queueG Σ}
  (back front : loc) (q : list (val * val)) : iProp Σ :=
  match q with
  |[] => ⌜back = front⌝
  |(m, drop) :: q => ∃ (l : loc),
    front ↦ cons ∗ (front +ₗ 1) ↦ m ∗ (front +ₗ 2) ↦ drop ∗
      (front +ₗ 3) ↦ #l ∗ is_queue_list back l q
  end.

Local Instance is_queue_list_timeless `{heapGS Σ, queueG Σ} back front q : Timeless (is_queue_list back front q).
Proof. move:q front. by elim=>[|[]]; apply _. Qed.

Definition N : namespace := nroot .@ "eactris_queue".

Local Definition queue_inv `{heapGS Σ, queueG Σ} (γback γfront γb γf γq γaf : gname) : iProp Σ :=
  ∃ (front back : loc) (q q' : list (val * val)) (s : QueueState) (cancelling : bool),
    γback ↪{#1/2} active_back s ∗
    γfront ↪{#1/2} (active_front s, cancelling) ∗
    γq ↪{#1/2} (if active_front s && negb cancelling then q else q') ∗
    γb ↪{#1/2} back ∗
    γf ↪ {#1/2} front ∗
    (⌜cancelling = active_front s⌝ ∨ token γaf) ∗
    (if active_front s then is_queue_list back front q else emp)∗
    (if active_front s && cancelling then [∗ list] '(_, drop) ∈ q, drop_spec drop else emp) ∗
    match active_back s, active_front s with
     | true, true => back ↦ nil
     | true, false => back ↦ cancelled
     | false, true => ∃ v1 v2 v3,
                       back ↦ cancelled ∗
                       (back +ₗ 1) ↦ v1 ∗
                       (back +ₗ 2) ↦ v2 ∗
                       (back +ₗ 3) ↦ v3 
     | false, false => emp end.

Definition is_queue_def `{heapGS Σ, queueG Σ} s (e d : loc) (q : list (val * val)) : iProp Σ :=
  ∃ (γback γfront γb γf γq γaf γcf γcb : gname),
  meta e N (γback, γfront, γb, γf, γq, γaf, γcb) ∗
  meta d N (γback, γfront, γb, γf, γq, γaf, γcf) ∗
  (if active_back s then γback ↪{#1/2} true else token γcb) ∗
  (if active_front s then γfront ↪{#1/2} (true, false) else
      token γaf ∗ token γcf) ∗
  γq ↪{#1/2} q.

Local Definition is_queue_aux : seal (@is_queue_def). Proof. by eexists. Qed.
Definition is_queue := is_queue_aux.(unseal).
Local Definition is_queue_unseal :
  @is_queue = @is_queue_def := is_queue_aux.(seal_eq).
Global Arguments is_queue {Σ _ _} s e d q.

Global Instance is_queue_timeless `{heapGS Σ, queueG Σ} s e d q : Timeless (is_queue s e d q).
Proof. rewrite is_queue_unseal. case:s=>[][][]; apply _. Qed.

Local Definition enqueue_handle_def `{heapGS Σ, queueG Σ} (e : loc) : iProp Σ :=
  ∃ (γback γfront γb γf γq γaf γcb : gname) (back : loc) (v1 v2 v3 : val),
    meta e N (γback, γfront, γb, γf, γq, γaf, γcb) ∗
    inv N (queue_inv γback γfront γb γf γq γaf) ∗
    token γcb ∗
    γb ↪{#1/2} back ∗
    e ↦ #back ∗
    (back +ₗ 1) ↦ v1 ∗
    (back +ₗ 2) ↦ v2 ∗
    (back +ₗ 3) ↦ v3.
Local Definition enqueue_handle_aux : seal (@enqueue_handle_def).
Proof. by eexists. Qed.
Definition enqueue_handle := enqueue_handle_aux.(unseal).
Local Definition enqueue_handle_unseal :
  @enqueue_handle = @enqueue_handle_def := enqueue_handle_aux.(seal_eq).
Global Arguments enqueue_handle {Σ _ _} e.

Definition enqueue_cancel_def `{heapGS Σ, queueG Σ} (e : loc) : iProp Σ :=
  ∃ (γback γfront γb γf γq γaf : gname) (back : loc) (v1 v2 v3 : val),
    inv N (queue_inv γback γfront γb γf γq γaf) ∗
    γback ↪{#1/2} true ∗
    γb ↪{#1/2} back ∗
    e ↦ #back ∗
    (back +ₗ 1) ↦ v1 ∗
    (back +ₗ 2) ↦ v2 ∗
    (back +ₗ 3) ↦ v3.
Local Definition enqueue_cancel_aux : seal (@enqueue_cancel_def).
Proof. by eexists. Qed.
Definition enqueue_cancel := enqueue_cancel_aux.(unseal).
Local Definition enqueue_cancel_unseal :
  @enqueue_cancel = @enqueue_cancel_def := enqueue_cancel_aux.(seal_eq).
Global Arguments enqueue_cancel {Σ _ _} e.

Local Definition dequeue_handle_def `{heapGS Σ, queueG Σ} (d : loc) : iProp Σ :=
  ∃ (γback γfront γb γf γq γaf γcf : gname) (front : loc),
    meta d N (γback, γfront, γb, γf, γq, γaf, γcf) ∗
    inv N (queue_inv γback γfront γb γf γq γaf) ∗
    token γcf ∗
    γf ↪{#1/2} front ∗
    d ↦ #front.
Local Definition dequeue_handle_aux : seal (@dequeue_handle_def).
Proof. by eexists. Qed.
Definition dequeue_handle := dequeue_handle_aux.(unseal).
Local Definition dequeue_handle_unseal :
  @dequeue_handle = @dequeue_handle_def := dequeue_handle_aux.(seal_eq).
Global Arguments dequeue_handle {Σ _ _} d.

Local Definition dequeue_cancel_def `{heapGS Σ, queueG Σ} (d : loc) : iProp Σ :=
  ∃ (γback γfront γb γf γq γaf : gname) (front : loc),
    inv N (queue_inv γback γfront γb γf γq γaf) ∗
    γfront ↪{#1/2} (true, true) ∗
    γf ↪{#1/2} front ∗
    d ↦ #front.
Local Definition dequeue_cancel_aux : seal (@dequeue_cancel_def).
Proof. by eexists. Qed.
Definition dequeue_cancel := dequeue_cancel_aux.(unseal).
Local Definition dequeue_cancel_unseal :
  @dequeue_cancel = @dequeue_cancel_def := dequeue_cancel_aux.(seal_eq).
Global Arguments dequeue_cancel {Σ _ _} d.

Section lemmas.

  Context `{heapGS Σ, queueG Σ}.

  Lemma cancel_enqueue s e d q :
    enqueue_handle e -∗
    is_queue s e d q -∗
    enqueue_cancel e ∗ is_queue {| active_front := active_front s; active_back := false |} e d q.
  Proof.
    rewrite enqueue_cancel_unseal enqueue_handle_unseal is_queue_unseal.
    iSteps as (γback γfront γb γf γq γaf γcb back ????????? γcf ?)
      "meta ctx meta' ? token γb e back1 back2 back3 γback γfront γq".
    iDestruct (meta_agree with "meta meta'") as %h. move:h=>[<-<-<-<-<-<-<-].
    iClear "meta'".
    case: (active_back s); last by iCombine "token γback" gives %abs.
    by iSteps.
  Qed.

  Lemma cancel_dequeue d (E : coPset) :
    ↑N ⊆ E →
    dequeue_handle d ={E, E ∖ ↑N}=∗
      ∀ s e q, is_queue s e d q -∗ (▷ [∗ list] '(_, drop) ∈ q, drop_spec drop) -∗
        |={∅}=> is_queue {| active_front := false; active_back := active_back s |} e d [] ∗
        |={E ∖ ↑N, E}=> dequeue_cancel d.
  Proof.
    rewrite dequeue_cancel_unseal dequeue_handle_unseal is_queue_unseal.
    iStep 2 as (NE γback γfront γb γf γq γaf γcf front) "meta ctx token γf d".
    iInv "ctx" as (? back q q' s c) "(>γback & >γfront & >γq & >γb & >γf' & >γaf & queue & _ & back)" "close".
    iIntros "!>" (s' e ?) "is_queue drops".
    iDecompose "is_queue" as (??????? γcb) "? meta' γback' γfront' γq'".
    iDestruct (meta_agree with "meta meta'") as %h. move:h=>[<-<-<-<-<-<-<-].
    iClear "meta'". clear.
    case front_s': (active_front s'); last first.
    { iDestruct "γfront'" as "(_ & abs)". by iCombine "token abs" gives %abs. }
    iDestruct (ghost_var_agree with "γfront γfront'") as %[->->]%pair_eq.
    iDestruct (ghost_var_agree with "γq γq'") as %<-.
    iDestruct (ghost_var_agree with "γf γf'") as %<-.
    iDestruct "γaf" as "[%abs|γaf]"; first done.
    iMod (ghost_var_update_halves (true, true) with "γfront γfront'") as "(γfront & γfront')".
    iMod (ghost_var_update_halves [] with "γq γq'") as "(γq & γq')".
    iSplitR "close γback γfront' γq' γb γf' queue back drops d γfront γf"; first by iSteps.
    iModIntro.
    iMod ("close" with "[γback γfront' γq' γb γf' queue back drops]") as "_"; last by iSteps.
    iExists _, _, _, [], {| active_front := true; active_back := active_back s |}. by iSteps.
  Qed.

  Lemma is_queue_list_app back l front q1 q2 :
    is_queue_list l front q1 -∗ is_queue_list back l q2 -∗
    is_queue_list back front (q1 ++ q2).
  Proof.
    iIntros "q1 q2".
    iInduction q1 as [|[] q1] "IH" forall (front);
      first by iDestruct "q1" as %<-.
    iDecompose "q1". by iSteps.
  Qed.

  Lemma is_queue_list_snoc (back front l : loc) q m drop :
    l ↦ cons -∗ (l +ₗ 1) ↦ m -∗ (l +ₗ 2) ↦ drop -∗
    (l +ₗ 3) ↦ #back -∗ is_queue_list l front q -∗
    is_queue_list back front (q ++ [(m, drop)]).
  Proof.
    iSteps as "l l1 l2 l3 queue".
    iApply (is_queue_list_app with "queue").
    by iSteps.
  Qed.

  Lemma get_drop_spec (drop : val) :
    WP drop #() {{ _, True }} ⊢ drop_spec drop.
  Proof.
    rewrite drop_spec_unseal.
    iSteps. iExists True%I, True%I, ∅.
    iSplitL; last by iSteps. iSteps as (??) "AU". iMod "AU" as "(_ & (_ & H))".
    by iMod ("H" with "[//] [//]") as "$".
  Qed.

  Lemma get_drop_spec' (drop : val) (P Q : iProp Σ) (E : coPset) :
    AU <{ P }> @ ⊤ ∖ E, ∅ <{ Q, COMM True }> -∗
    <<{ P }>> drop #() @E <<{ ∃∃ v, Q | RET v; True }>> -∗
    drop_spec drop.
  Proof.
    rewrite drop_spec_unseal. iStep 2. by iFrame.
  Qed.

End lemmas.

Section queue_spec.

  Context `{!heapGS Σ, !queueG Σ}.

  Set Default Proof Using "Type".

  Local Instance array_free_4_spec l v v1 v2 v3 :
    SPEC {{ l ↦ v ∗ (l +ₗ 1) ↦ v1 ∗ (l +ₗ 2) ↦ v2 ∗ (l +ₗ 3) ↦ v3 }}
      array_free #l #4
    {{ RET #(); emp }}.
  Proof.
    iSteps as "l l1 l2 l3".
    by wp_apply (wp_array_free _ _ _ [v; v1; v2; v3] 4 with
        "[l l1 l2 l3]") as "_"; [|iSteps..].
  Qed.

  Global Instance qnil_spec :
    SPEC {{ True }}
      qnil #()
    {{ (l : loc), RET #l;
        l ↦ nil ∗ (l +ₗ 1) ↦ #() ∗ (l +ₗ 2) ↦ #() ∗ (l +ₗ 3) ↦ #() }}.
  Proof. iSteps. Qed.

  Global Instance new_queue_spec :
    SPEC {{ True }}
      new_queue #()
    {{ (e d : loc), RET (#e, #d)%V;
        is_queue {| active_front := true; active_back := true |} e d [] ∗
        enqueue_handle e ∗ dequeue_handle d }}.
  Proof.
    rewrite is_queue_unseal enqueue_handle_unseal dequeue_handle_unseal.
    iStep 12 as (back) "back back1 back2 back3 £".
    iMod (ghost_var_alloc back) as (γf) "(γf & γf')".
    iMod (ghost_var_alloc back) as (γb) "(γb & γb')".
    iModIntro.
    wp_smart_apply (wp_alloc with "[//]") as (d) "(d & meta_d)".
    wp_smart_apply (wp_alloc with "[//]") as (e) "(e & meta_e)".
    iMod (ghost_var_alloc true) as (γback) "(γback & γback')".
    iMod (ghost_var_alloc (true, false)) as (γfront) "(γfront & γfront')".
    iMod (ghost_var_alloc []) as (γq) "(γq & γq')".
    iMod token_alloc as (γcb) "γcb".
    iMod token_alloc as (γaf) "γaf".
    iMod token_alloc as (γcf) "γcf".
    iMod (meta_set _ _ (γback, γfront, γb, γf, γq, γaf, γcf) N with "meta_d") as "#meta_d"; first done.
    iMod (meta_set _ _ (γback, γfront, γb, γf, γq, γaf, γcb) N with "meta_e") as "#meta_e"; first done.
    iMod (inv_alloc N _ (queue_inv γback γfront γb γf γq γaf) with "[γback γfront γq γb γf γaf back]") as "inv".
    { iSteps. iExists {| active_front := true; active_back := true |}. iSteps. apply []. }
    by iSteps.
  Qed.

  Global Instance enqueue_spec e (m drop : val) :
    SPEC ⟨ ↑N ⟩ s d P q n,
      << enqueue_handle e ¦ (if active_front s then emp else (P ∧ drop_spec drop)) ∗
          is_queue s e d q ∗ steps_lb n >>
      enqueue #e m drop
    << RET #(); enqueue_handle e ¦
       is_queue s e d (q ++ [(m, drop)]) ∗ steps_lb (S n) ∗ £ n >>.
  Proof.
    rewrite enqueue_handle_unseal is_queue_unseal/enqueue/is_queue_def drop_spec_unseal.
    iStep 73 as (Φ γback γfront γb γf γq γaf γcb back _ _ _ l)
      "meta ctx token γb AU l l1 l2 l3 e back1 back2 back3 (£1 & £2 & £)".
    iModIntro. wp_bind (CmpXchg _ _ _).
    iInv "ctx" as (front ? q q' s c) "(>γback & >γfront & >γq & >γb' & >γf & >γaf
      & queue & drops & back)" "close_ctx".
    iMod (lc_fupd_elim_later with "£2 drops") as "drops".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iMod "AU" as (s' d P ? n) "((drop & is_queue & #steps) & (_ & close))".
    iDecompose "is_queue" as (?????? γcf ?) "meta' ? γback' γfront' γq'".
    iDestruct (meta_agree with "meta meta'") as %h. move:h=>[<-<-<-<-<-<-<-]. clear.
    iClear "meta'".
    iApply (wp_lb_update with "steps").
    case: (active_back s'); last by iCombine "token γback'" gives %abs.
    iDestruct (ghost_var_agree with "γback γback'") as %->.
    case: (active_front s').
    - iDestruct (ghost_var_agree with "γq γq'") as %<-.
      iMod (ghost_var_update_halves (q ++ [ (m, drop) ]) with "γq γq'") as "(γq & γq')".
      iMod (ghost_var_update_halves l with "γb γb'") as "(γb & γb')".
      iDestruct (ghost_var_agree with "γfront γfront'") as %[->->]%pair_eq.
      wp_apply (wp_cmpxchg_suc_lc with "[$back $steps]"); [done|by left|].
      iStep 3 as "steps' back £".
      iMod ("close" with "[$γback' $γfront' γq' £]") as "Φ"; first by iSteps.
      iDestruct "γaf" as "[%abs|γaf]"; first done.
      iMod ("close_ctx" with "[γback γfront γq γb γf queue back back1 back2 back3 l γaf]") as "_";
        last by iSteps.
      iSteps. iExists {| active_front := true; active_back := true |}. iSteps.
      iSplitR "l"; last by iFrame.
      by iApply (is_queue_list_snoc with "back back1 back2 back3 queue").
    - iDestruct "γfront'" as "(γaf' & γcf)".
      iDestruct "γaf" as "[->|γaf]"; last by iCombine "γaf γaf'" gives %abs.
      iDestruct "drop" as "(_ & drop)".
      iDestruct (ghost_var_agree with "γq γq'") as %<-.
      rewrite andb_negb_r.
      iMod (ghost_var_update_halves (q' ++ [(m, drop)]) with "γq γq'") as "(γq & γq')".
      case: (active_front s).
      + wp_apply (wp_cmpxchg_suc_lc with "[$back $steps]"); [done|by left|].
        iStep 2 as "steps' back £".
        iMod (ghost_var_update_halves l with "γb γb'") as "(γb & γb')".
        iMod ("close" with "[$γback' $γaf' $γcf γq' £]") as "Φ"; first by iSteps.
        iMod ("close_ctx" with "[γback γfront γq γb' γf back queue
          back1 back2 back3 l drops drop]") as "_"; last by iSteps.
        iSteps. iExists {| active_front := true; active_back := true |}. iSteps.
        iExists (q ++ [(m, drop)]).
        iSplitR "l drops drop"; first by iApply (is_queue_list_snoc with "back back1 back2 back3 queue").
        iFrame "l". iApply big_sepL_snoc. rewrite drop_spec_unseal. by iFrame.
      + wp_apply (wp_cmpxchg_fail_lc with "[$back $steps]"); [done|by left|].
        iStep 2 as "steps' back £".
        iMod ("close" with "[$γback' $γaf' $γcf γq' £]") as "Φ"; first by iSteps.
        iSteps. iExists {| active_front := false; active_back := true |}. iSteps. iExists [].
        iDecompose "drop" as (? ? ?) "drop AU".
        iSteps. iExists (λ _, emp)%I. by iSplitL "AU"; iSteps.
  Qed.

  Global Instance dequeue_spec d :
    SPEC ⟨ ↑N ⟩ s e q,
      << dequeue_handle d ¦ is_queue s e d q >>
        dequeue #d
      << (om : val), RET om;
          dequeue_handle d ¦
          match q with
              | [] => ⌜om = NONEV⌝ ∗ ⌜active_back s = false⌝ ∗ is_queue s e d []
              | (m, _) :: q' => ⌜om = SOMEV m⌝ ∗ is_queue s e d q'
          end >>.
  Proof.
    rewrite dequeue_handle_unseal is_queue_unseal/dequeue/is_queue_def.
    iStep as (Φ) "". iLöb as "IH".
    iSteps as (γback γfront γb γf γq γaf γcf front) "meta ctx IH token γf AU d £".
    iInv "ctx" as (? back q ? s c) "(>γback & >γfront & >γq & >γb & >γf' & >γaf &
      queue & drops & back)" "close_ctx".
    iDestruct (ghost_var_agree with "γf γf'") as %<-.
    iMod "AU" as (s' e ?) "(is_queue & close)".
    iDecompose "is_queue" as (??????? γcb) "? meta' γback' γfront' γq'".
    iDestruct (meta_agree with "meta meta'") as %h. move:h=>[<-<-<-<-<-<-<-]. clear.
    iClear "meta'".
    iDestruct (ghost_var_agree with "γq γq'") as %<-.
    case: (active_front s'); last first.
    { iDestruct "γfront'" as "(_ & abs)". by iCombine "token abs" gives %abs. }
    iDestruct (ghost_var_agree with "γfront γfront'") as %[->->]%pair_eq.
    iDestruct "γaf" as "[%abs|γaf]"; first done.
    case : q =>[|[m drop] q].
    - iDestruct "queue" as "> <-".
      case: (active_back s).
      + iStep 2 as "front". iDestruct "close" as "(repeat & _)".
        iMod ("repeat" with "[γback' γfront' γq']") as "AU"; first by iSteps. clear.
        iSteps. iExists {| active_front := true; active_back := true|}. iSteps. iExists [].
        iStep 14. iModIntro. iSplitL; last by iSteps.
        iSplitR; first by iSteps. by iSplitL "d γf token"; iSteps.
      + iClear "IH". iDestruct "close" as "(_ & close)".
        iSteps as (???) "back1 back2 back3 back".
        case: (active_back s'); first by iCombine "γback γback'" gives %[_ abs].
        iMod ("close" with "[γback' γfront' γq' £]") as "Φ"; first by iSteps.
        iExists {| active_front := true; active_back := false |}. iSteps.
        iExists []. by iSteps.
    - iClear "IH". iDestruct "close" as "(_ & close)".
      iDecompose "queue" as (l) "front front1 front2 front3 queue".
      iMod (ghost_var_update_halves l with "γf γf'") as "(γf & γf')".
      iMod (ghost_var_update_halves q with "γq γq'") as "(γq & γq')".
      iStep 2 as "back front".
      iMod ("close" with "[γback' γfront' γq' £]") as "Φ"; first by iSteps.
      iMod ("close_ctx" with "[γback γfront γq γb γf queue back γaf]") as "_"; last by iSteps.
      iModIntro. iExists _, _, _, [], {| active_front := true; active_back := active_back s |}. by iSteps.
  Qed.

  Global Instance cancel_back_spec e :
    SPEC
    {{ enqueue_cancel e }}
      cancel_back #e
    {{ RET #(); emp }}.
  Proof.
    rewrite enqueue_cancel_unseal.
    iSteps as (γback γfront γb γf γq γaf back ???) "ctx γback γb back1 back2 back3 _".
    iInv "ctx" as (front ? q ? s c) "(>γback' & >γfront & >γq & >γb' & >γf & >γaf &
      queue & drops & back)" "close_ctx".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDestruct (ghost_var_agree with "γback γback'") as %<-.
    iMod (ghost_var_update_halves false with "γback γback'") as "(γback & γback')".
    case: (active_front s).
    - iSteps. iExists {| active_front := true; active_back := false |}. by iSteps.
    - iSteps. iExists {| active_front := false; active_back := false |}.
      by iSteps; iExists []; iSteps.
  Qed.

  Global Instance cancel_front_spec d :
    SPEC {{ dequeue_cancel d }}
      cancel_front #d
    {{ RET #(); emp }}.
  Proof.
    rewrite dequeue_cancel_unseal.
    iSteps as (γback γfront γb γf γq γaf front) "ctx γfront γf d".
    iLöb as "IH" forall (front).
    rewrite/cancel_front. iSteps as "IH d (£1 & £)".
    iInv "ctx" as (? back q ? s c) "(>γback & >γfront' & >γq & >γb & >γf' & _ &
      queue & drops & back)" "close_ctx".
    iDestruct (ghost_var_agree with "γf γf'") as %<-.
    iDestruct (ghost_var_agree with "γfront γfront'") as %[<-<-]%pair_eq.
    case: q=>[|[m drop] q].
    - iDestruct "queue" as "> <-".
      iMod (ghost_var_update_halves (false, false) with "γfront γfront'") as "(γfront & γfront')".
      case: (active_back s).
      + iSteps. iExists {| active_front := false; active_back := true |}. iSteps. iExists []. by iSteps.
      + iSteps. iExists {| active_front := false; active_back := false |}. iSteps. iExists []. by iSteps.
    - rewrite drop_spec_unseal/=. iMod (lc_fupd_elim_later with "£1 drops") as "(drop & drops)".
      iDecompose "drop" as (???) "drop AU".
      iDecompose "queue" as (l) "front front1 front2 front3 queue".
      iMod (ghost_var_update_halves l with "γf γf'") as "(γf & γf')".
      iStep 4 as (_) "back front".
      iMod ("close_ctx" with "[γback γfront' γq γb γf' queue drops back]") as "_".
      { iExists _, _, _, _, {| active_front := true; active_back := active_back s |}. iSteps.
        rewrite drop_spec_unseal. by iSteps. }
      iSteps. iExists (λ _, emp)%I. by iSplitL "AU"; iSteps.
  Qed.

End queue_spec.