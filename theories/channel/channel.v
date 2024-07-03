From iris.heap_lang Require Export primitive_laws notation proofmode.
From eactris.channel Require Export proto.
From diaframe.heap_lang Require Import proof_automation.
From diaframe.lib Require Import atomic.
From diaframe.symb_exec Require Import atom_spec_notation.
From eactris.utils Require Import ghost_var.
From eactris.channel Require Export atomic_channel.
From iris.base_logic.lib Require Import token.
Import queue atomic_channel.

Definition V : Type := option (val * val * gname).

Notation iProto Σ := (iProto Σ V).
Notation iMsg Σ := (iMsg Σ V).

Class chanG Σ := {
  chanG_queueG :: queue.queueG Σ;
  chanG_protoG :: protoG Σ V;
  chanG_activeG :: ghost_varG Σ bool
}.
Definition chanΣ : gFunctors :=
  #[ queue.queueΣ; protoΣ V; ghost_varΣ bool].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Definition N := nroot .@ "eactris_channel".

Definition iProto_inv `{!heapGS Σ, !chanG Σ} γb γf (c c' : val) γ γ' : iProp Σ :=
  ∃ (q q' : list (val * val)) (b f : bool),
    let to_V g l := (λ v, Some (v, g)) <$> l in
    let df := if b then DfracOwn (1/2) else DfracDiscarded in
    let df' := if f then DfracOwn (1/2) else DfracDiscarded in
    let qp := if b || (negb f) then to_V γf q else to_V γf q ++ [None] in
    let qp' := if f || (negb b) then to_V γb q' else to_V γb q' ++ [None] in
    γb ↪{df} b ∗ γf ↪{df'} f ∗
    (if b || f then
      is_chan c c' {| active_front := f; active_back := b|} q q' ∗ iProto_ctx γ γ' qp qp' else emp) ∗
    steps_lb (length q) ∗ steps_lb (length q') ∗
    (if b then £ (2 + 3 * length q') else emp) ∗
    (if f then £ (2 + 3 * length q) else emp).

Definition iProto_pointsto_def `{!heapGS Σ, !chanG Σ} (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γb γf c' γ γ',
    γb ↪{#1/2} true ∗
    chan_handle c ∗
    iProto_own γ p ∗
    inv N (iProto_inv γb γf c c' γ γ').

Definition iProto_pointsto_aux : seal (@iProto_pointsto_def). Proof. by eexists. Qed.
Definition iProto_pointsto := iProto_pointsto_aux.(unseal).
Local Definition iProto_pointsto_unseal :
  @iProto_pointsto = @iProto_pointsto_def := iProto_pointsto_aux.(seal_eq).
Arguments iProto_pointsto {_ _ _} c p.
Global Instance: Params (@iProto_pointsto) 4 := {}.
Notation "c ↣ p" := (iProto_pointsto c p)
  (at level 20, format "c  ↣  p").

Definition iEMsg_base_def `{!heapGS Σ, !chanG Σ} (v : val) (P : iProp Σ) (p : iProto Σ) : iMsg Σ :=
  ∃ drop γf, MSG Some (v, drop, γf) {{ P ∧ drop_spec drop ∨ γf ↪□ false }}; p.
Definition iEMsg_base_aux : seal (@iEMsg_base_def). by eexists. Qed.
Definition iEMsg_base := iEMsg_base_aux.(unseal).
Definition iEMsg_base_eq : @iEMsg_base = @iEMsg_base_def := iEMsg_base_aux.(seal_eq).
Arguments iEMsg_base {_ _ _} v P p.
Global Instance: Params (@iEMsg_base) 3 := {}.

Notation "'EMSG' v {{ P } } ; p" := (iEMsg_base v P p)
  (at level 200, v at level 20, right associativity,
   format "EMSG  v  {{  P  } } ;  p") : msg_scope.
Notation "'EMSG' v ; p" := (EMSG v {{ True }}; p)%msg
  (at level 200, v at level 20, right associativity,
   format "EMSG  v ;  p") : msg_scope.

Section prot.

  Context `{!heapGS Σ, !chanG Σ}.

  Definition cancel_prot_def_aux (rec : iProto Σ) : iProto Σ :=
    <! v> EMSG v; rec.
  Global Instance cancel_prot_aux_contractive : Contractive cancel_prot_def_aux.
  Proof. rewrite /cancel_prot_def_aux iEMsg_base_eq/iEMsg_base_def/=. solve_proto_contractive. Qed.
  Definition cancel_prot_def Q : iProto Σ := <?> MSG None {{ Q }}; fixpoint cancel_prot_def_aux.
  Definition cancel_prot_aux : seal (@cancel_prot_def). by eexists. Qed.
  Definition cancel_prot := cancel_prot_aux.(unseal).
  Local Definition cancel_prot_unseal : @cancel_prot = @cancel_prot_def := cancel_prot_aux.(seal_eq).

  Definition send_or_cancel Q m : iProto Σ :=
    <! (b : bool)> if b then m else MSG None {{ Q }}; (iProto_dual (fixpoint cancel_prot_def_aux)).

  Lemma iEMsg_map_base f v P p :
    NonExpansive f →
    iMsg_map f (EMSG v {{ P }}; p) ≡ (EMSG v {{ P }}; (f p))%msg.
  Proof.
    rewrite iEMsg_base_eq/iEMsg_base_def iMsg_exist_eq iMsg_base_eq/= =>???.
    iSplit.
    + iIntros "(% & (% & % & <- & eq & $) & eq')".
      iSplitR; first done. iRewrite "eq'".
      iModIntro. by iRewrite "eq".
    + iIntros "(% & % & <- & #eq & $)". iExists p. by iRewrite -"eq".
  Qed.

  Lemma iEMsg_dual_base v P p :
    iMsg_dual (EMSG v {{ P }}; p) ≡ (EMSG v {{ P }}; (iProto_dual p))%msg.
  Proof. apply iEMsg_map_base, _. Qed.

  Lemma zap_send Q v : ⊢ cancel_prot Q ⊑ <!> EMSG v; cancel_prot Q.
  Proof.
    rewrite cancel_prot_unseal /cancel_prot_def {1}fixpoint_unfold/cancel_prot_def_aux.
    iApply iProto_le_swap. rewrite {3}iEMsg_base_eq/iEMsg_base_def/= {3 4}iMsg_exist_eq iMsg_base_eq.
    iIntros (????) "(<- & eq & Q) (%drop & %γf & <- & eq' & H)".
    iExists (<! (v0 : val)> EMSG v0; fixpoint cancel_prot_def_aux). iSplitL "eq H".
    { iModIntro. iRewrite -"eq". iExists v. iApply iProto_le_send.
      iIntros (??) "(<- & eq & _)". iExists _. iSplitR; first by iApply iProto_le_refl.
      rewrite {2}iEMsg_base_eq /iEMsg_base_def {2 3}iMsg_exist_eq. iExists drop, γf.
      rewrite iMsg_base_eq. iSplitR; first done. iFrame "H". by rewrite {2}fixpoint_unfold.
    }
    iModIntro. iRewrite -"eq'".
    iApply iProto_le_recv. iSteps as (?) "eq". iExists (fixpoint cancel_prot_def_aux).
    iSplitL "eq".
    { iModIntro. iRewrite -"eq". rewrite {3}fixpoint_unfold/cancel_prot_def_aux. by iApply iProto_le_refl. }
    by iSteps.
  Qed.

  Lemma send_or_cancel_swap Q v1 v2 p :
    ⊢ (<?> EMSG v1; send_or_cancel Q (EMSG v2; p)) ⊑
      (send_or_cancel Q (EMSG v2; <?> EMSG v1; p)).
  Proof.
    rewrite iEMsg_base_eq/iEMsg_base_def iMsg_base_eq.
    iIntros (drop γf b) "". iApply iProto_le_swap.
    iIntros (????) "(<- & eq & H) H'".
    case: b.
    + rewrite iMsg_exist_eq. iDestruct "H'" as (??) "(<- & eq' & H')".
      iExists p. iSplitL "eq H'".
      { iNext. iRewrite -"eq". iExists true. iApply iProto_le_send.
        rewrite iMsg_base_eq. iIntros (??) "(<- & eq & _)". iExists p.
        iSplitL "eq". { iNext. iRewrite "eq". iApply iProto_le_refl. }
        iExists _, _. by iFrame "H'". }
      iNext. iRewrite -"eq'". iApply iProto_le_recv.
      rewrite iMsg_base_eq. iIntros (??) "(<- & eq & _)". iExists p.
      iSplitL "eq". { iNext. iRewrite "eq". iApply iProto_le_refl. }
      iExists drop, γf. by iFrame "H".
    + rewrite iMsg_base_eq. iDestruct "H'" as "(<- & eq' & Q)".
      iExists (iProto_dual (fixpoint cancel_prot_def_aux)). iSplitL "eq Q".
      { iNext. iRewrite -"eq". iExists false. rewrite -iMsg_base_eq.
        by iApply (iProto_le_payload_intro_l with "Q"). }
      iNext. iRewrite -"eq'". rewrite {2}fixpoint_unfold iProto_dual_message.
      iApply iProto_le_recv. iIntros (??) "(<- & eq & _)". iExists _.
      iSplitL "eq". { iNext. iRewrite -"eq". iApply iProto_le_refl. }
      iExists (fixpoint cancel_prot_def_aux). iSplitL; last done.
      rewrite iEMsg_base_eq/iEMsg_base_def iMsg_base_eq iMsg_exist_eq.
      iExists _, _, _. by iFrame "H".
  Qed.

  Lemma send_or_cancel_send Q m : ⊢ send_or_cancel Q m ⊑ <!> m.
  Proof. iExists true. iApply iProto_le_refl. Qed.

  Lemma send_or_cancel_cancel Q m : ⊢ send_or_cancel Q m ⊑ iProto_dual (cancel_prot Q).
  Proof.
    iExists false. rewrite cancel_prot_unseal iProto_dual_message iMsg_dual_base.
    iApply iProto_le_refl.
  Qed.

End prot.

Notation "↯" := (fixpoint cancel_prot_def_aux) (at level 200) : proto_scope.

Definition cancellable `{!heapGS Σ, !chanG Σ} (c : val) : iProp Σ :=
  ∃ c' q,
    chan_handle c ∗ is_chan c c' {| active_front := false; active_back := true |} q [].

Notation "↯ Q" := (cancel_prot Q) (at level 200, Q at level 20) : proto_scope.

Notation "'CANCEL' Q" := (iProto_dual (↯ Q))%proto (at level 200, Q at level 20) : proto_scope.

Notation "<!↯ | Q > m" := (send_or_cancel Q m) (at level 200, m at level 200, Q at level 20) : proto_scope.

Notation "<!↯ x1 .. xn | Q > m" := (<!↯ | Q > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<!↯  x1  ..  xn  |  Q  >  m") : proto_scope.
Notation "<!↯.. x1 .. xn | Q > m" := (<!↯ | Q > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<!↯..  x1  ..  xn  |  Q  >  m") : proto_scope.
Notation "<!↯ x1 .. xn > m" := (<!↯ | True > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!↯  x1  ..  xn  >  m") : proto_scope.
Notation "<!↯.. x1 .. xn > m" := (<!↯ | True > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<!↯..  x1  ..  xn  >  m") : proto_scope.

Notation "<?↯ | Q > m" := (iProto_dual (send_or_cancel Q (iMsg_dual m)))
  (at level 200, m at level 200, Q at level 20) : proto_scope.

Notation "<?↯ x1 .. xn | Q > m" := (<?↯ | Q > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<?↯  x1  ..  xn  |  Q  >  m") : proto_scope.
Notation "<?↯.. x1 .. xn | Q > m" := (<?↯ | Q > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<?↯..  x1  ..  xn  |  Q  >  m") : proto_scope.
Notation "<?↯ x1 .. xn | Q > m" := (<?↯ | Q > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<?↯  x1  ..  xn  |  Q  >  m") : proto_scope.
Notation "<?↯.. x1 .. xn | Q > m" := (<?↯ | Q > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200, Q at level 20,
   format "<?↯..  x1  ..  xn  |  Q  >  m") : proto_scope.

Section specs.

  Set Default Proof Using "Type".
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types TT : tele.

  Lemma iProto_inv_sym γb γf c c' γ γ' :
    iProto_inv γb γf c c' γ γ' ⊢ iProto_inv γf γb c' c γ' γ.
  Proof.
    iSteps as (q q' b f) "?? chan £ £'".
    case b.
    + iDecompose "chan" as "chan ctx".
      iPoseProof (is_chan_sym with "chan") as "chan".
      iPoseProof (iProto_ctx_sym with "ctx") as "ctx".
      rewrite orb_true_r. by iSteps.
    + case f; last by iSteps.
      iDecompose "chan" as "chan ctx".
      iPoseProof (is_chan_sym with "chan") as "chan".
      iPoseProof (iProto_ctx_sym with "ctx") as "ctx".
      by iSteps.
  Qed.

  Lemma iProto_pointsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_pointsto_unseal.
    iStep 2 as (?????) "inv γb c γ sub".
    iFrame "c γb inv".
    by iApply (iProto_own_le with "γ").
  Qed.

  Global Instance new_chan_spec p :
    SPEC {{ emp }}
      new_chan #()
    {{ (c c' : val), RET (c, c')%V; c ↣ p ∗ c' ↣ iProto_dual p }}.
  Proof.
    rewrite iProto_pointsto_unseal.
    iStep 9 as (c c') "chan c c' £".
    iMod (iProto_init p) as (γ γ') "(ctx & γ & γ')".
    iMod (ghost_var_alloc true) as (γb) "(γb & γb')".
    iMod (ghost_var_alloc true) as (γf) "(γf & γf')".
    iMod steps_lb_0 as "steps".
    iMod lc_zero as "#£0".
    iMod (inv_alloc N _ (iProto_inv γb γf c c' γ γ') with "[chan ctx γb' γf' steps £]") as "#inv".
    { iSteps. iExists true. iSteps. iExists true. by iSteps. }
    iFrame "c γ γb". iSplitR; first by iFrame "inv".
    iFrame "c' γ' γf". iExists γb, c, γ. iModIntro.
    iApply (inv_alter with "inv").
    iStep 2. iIntros "H". iSplitL "H"; first by iApply iProto_inv_sym.
    iIntros "H". by iApply iProto_inv_sym.
  Qed.

  Global Instance send_spec {TT} tt c v (drop : val) P p :
    SPEC {{ c ↣ (<!.. (x : TT)> EMSG v x {{ P x }}; p x) ∗ (P tt ∧ drop_spec drop) }}
      send c (v tt) drop
    {{ RET #(); c ↣ p tt }}.
  Proof.
    iSteps as "c P". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx".
    iFrame "chan". iExists (P tt), (max (length q) (length q')).
    case : f.
    + iSplitR. { iSteps. by case: (Nat.max_dec (length q) (length q'))=>->. }
      iSteps as_anon/ as "steps_max chan (£0 & £1 & £2 & £3 & £4)".
      { iExists true. iSteps. iExists true. by iSteps. }
      iMod (lc_fupd_elim_later with "£0 ctx") as "ctx".
      iMod (iProto_send _ _ _ _ _ (Some (v tt, drop, γf)) (p tt) with "ctx γ [P]") as "(ctx & proto)".
      { iApply iMsg_texist_exist. rewrite iEMsg_base_eq/iEMsg_base_def iMsg_exist_eq iMsg_base_eq. iExists tt, drop, γf.
        iFrame "P". by iSteps. }
      rewrite fmap_length.
      iPoseProof (lc_weaken (length q') with "£4") as "£4"; first by lia.
      iMod (later_credits.lc_fupd_elim_laterN with "£4 ctx") as "ctx".
      iExists true. iSteps. iExists true. iSteps. rewrite fmap_snoc app_length. iSteps.
      iSplitR. { iIntros "!>!>". iApply (steps_lb_le with "steps_max"). lia. }
      iSteps. iSplitL "£' £1 £2 £3"; last by iSteps. iDestruct "£'" as ">£".
      iCombine "£ £1 £2 £3" as "£". iApply (lc_weaken with "£"). lia.
    + iDestruct "γf" as "#γf".
      iSplitL "P". { iSteps. by case: (Nat.max_dec (length q) (length q'))=>->. }
      iSteps as_anon/ as "steps_max chan (£0 & £1 & £2 & £3 & £4)".
      { iExists true. iSteps. iExists false. by iSteps. }
      iMod (lc_fupd_elim_later with "£0 ctx") as "ctx".
      iMod (iProto_send _ _ _ _ _ (Some (v tt, drop, γf)) (p tt) with "ctx γ []") as "(ctx & proto)".
      { rewrite iEMsg_base_eq/iEMsg_base_def iMsg_base_eq iMsg_exist_eq/=. iApply iMsg_texist_exist.
        iExists tt, drop. iFrame "γf". by iSteps. }
      iPoseProof (lc_weaken (length q') with "£4") as "£4"; first by lia.
      iExists true. iSteps. iExists false. iSteps.
      rewrite app_length fmap_length/= (Nat.add_comm _ 1) fmap_snoc. iCombine "£4 £3" as "£4".
      iMod (later_credits.lc_fupd_elim_laterN with "£4 ctx") as "ctx".
      iSteps. rewrite app_length/=. iSplitR.
      { iIntros "!>!>". iApply (steps_lb_le with "steps_max"). lia. }
      by iSteps.
  Qed.

  Global Instance recv_spec {TT} c v P p :
    SPEC {{ c ↣ (<?.. (x : TT)> EMSG v x {{ P x }}; p x) }}
      recv c
    {{ tt, RET (SOMEV (v tt)); c ↣ (p tt) ∗ P tt }}.
  Proof.
    iSteps as "c". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx". iFrame "chan".
    iSteps as_anon / as (?) "q' (£1 & £2 & £3)".
    { iExists true. by iSteps. }
    case: q'=>[|[m drop] q'].
    + iDecompose "q'" as "γf ctx chan".
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iEMsg_base_eq/iEMsg_base_def iMsg_base_eq iMsg_exist_eq.
      iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & P)".
      by iDestruct (iMsg_texist_exist with "P") as (tt ??) "(% & eq & P)".
    + iDecompose "q'" as "chan".
      have -> : ∀ A (b : bool) (a : A) l l', (if b then a :: l else a :: l') = a :: if b then l else l'
        by move=>? [].
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iEMsg_base_eq/iEMsg_base_def iMsg_base_eq iMsg_exist_eq.
      iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & P)".
      iDestruct (iMsg_texist_exist with "P") as (tt ??) "(%h & eq & P)".
      move: h=>[<-->->].
      iDestruct "P" as "[(P & _)|abs]"; last by iDestruct (ghost_var_agree with "γb abs") as %abs.
      iPoseProof (later_equivI (p tt) p' with "eq") as "eq".
      iMod (lc_fupd_elim_later with "£3 eq") as "eq". iRewrite -"eq" in "γ".
      iExists true. iSteps. iSplitR.
      { iIntros "!>!>". iApply (steps_lb_le with "steps'"). lia. }
      by iSteps.
  Qed.

  Global Instance cancel_spec {TT} c Q :
    SPEC {{ c ↣ CANCEL Q ∗ Q }}
      cancel c
    {{ RET #(); emp }}.
  Proof.
    iSteps as "c Q". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx". iFrame "chan".
    iExists _, (γb ↪{#1/2} true ∗ iProto_ctx γ γ' (((λ v : val * val, Some (v, γf)) <$> q) ++ [None])
      (if f then [] else [None]))%I. iDestruct "£" as ">£".
    rewrite orb_false_r.
    iSplitL "ctx γ γb £ Q".
    {
      iCombine "ctx γ γb £ Q" as "H". iSplitL "H"; first by (iIntros "!>"; iApply "H").
      iIntros "!>(ctx & γ & γb & £ & Q)". iDestruct "£" as "(£1 & £2 & £ & £' & £'')". rewrite Nat.add_0_r.
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      rewrite cancel_prot_unseal iProto_dual_message iMsg_dual_base/=.
      iMod (iProto_send _ _ _ _ _ None (iProto_dual (fixpoint cancel_prot_def_aux)) with "ctx γ [Q]") as "(ctx & γ)".
      { rewrite iMsg_base_eq. by iSteps. }
      iAssert (£ (length (if f then (λ v : val * val, Some (v, γb)) <$> q'
                            else ((λ v : val * val, Some (v, γb)) <$> q') ++ [None]))) with "[£1 £'']" as "£''".
      { iCombine "£'' £1" as "£". iApply (lc_weaken with "£"). case: f; rewrite ?app_length fmap_length/=; lia. }
      iMod (later_credits.lc_fupd_elim_laterN with "£'' ctx") as "ctx".
      iInduction q' as [|[m drop] q'] "IH"; first by iSteps.
      rewrite {2}fixpoint_unfold iProto_dual_message
        iMsg_dual_exist iEMsg_base_eq/iEMsg_base_def iMsg_exist_eq iMsg_base_eq/=.
      have -> : ∀ (b : bool) A (a : A) l l', (if b then a :: l else a :: l') = a :: if b then l else l' by case.
      iMod (iProto_recv with "ctx γ") as (p) "H".
      iDestruct "£" as "(£1 & £)". iDestruct "£'" as "(£0 & £')".
      iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & (% & %p1 & (% & % & %eq & eq & drop) & eq'))".
      iPoseProof (later_equivI _ p1 with "eq") as "eq".
      iPoseProof (later_equivI p with "eq'") as "eq'".
      move: eq=>[_->->]. iCombine "eq eq'" as "eq".
      iMod (lc_fupd_elim_later with "£0 eq") as "(eq & eq')".
      iRewrite -"eq" in "eq'". iRewrite "eq'" in "γ".
      iDestruct "drop" as "[(_ & $)|abs]"; last by iDestruct (ghost_var_agree with "γb abs") as %abs.
      iApply ("IH" with "[] γb £ £' γ ctx"). iModIntro. iApply (steps_lb_le with "steps'"). lia.
    }
    iModIntro. iSplit.
    { iStep 2 as "chan ctx γ γb £ Q _". iFrame. iSteps. iExists true. iSteps. rewrite orb_false_r. by iSteps. }
    iIntros "(chan & γb & ctx)". iMod (ghost_var_update_halves false with "γb γb'") as "(γb & γb1)".
    iMod (ghost_var_persist with "γb") as "#γb". iMod steps_lb_0 as "steps_0".
    iSteps. iExists false. iSteps.
    by case: f; iSteps.
  Qed.

(*
  Not quite sure of how useful this could be


  Global Instance cancelled_recv_spec_continue c Q :
    SPEC {{ c ↣ ↯ Q }}
      recv c
    {{ RET NONEV; c ↣ ↯ Q }}.
  Proof.
    iSteps as "c". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx". iFrame "chan".
    iSteps as_anon / as (?) "q' (£1 & £2 & £3)".
    { iExists true. by iSteps. }
    case: q'=>[|[m drop] q'].
    + iDecompose "q'" as "γf ctx chan".
      iExists true. iSteps. iExists false. iSteps.
    + iDecompose "q'" as "chan".
      have -> : ∀ A (b : bool) (a : A) l l', (if b then a :: l else a :: l') = a :: if b then l else l'
        by move=>? [].
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      rewrite cancel_prot_unseal.
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iMsg_base_eq.
      by iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & (% & _))".
  Qed.

*)

  Global Instance cancelled_recv_spec c Q :
    SPEC {{ c ↣ ↯ Q }}
      recv c
    {{ RET NONEV; cancellable c ∗ Q }}.
  Proof.
    iSteps as "c". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx". iFrame "chan".
    iSteps as_anon / as (?) "q' (£1 & £2 & £3)".
    { iExists true. by iSteps. }
    case: q'=>[|[m drop] q'].
    + iDecompose "q'" as "γf ctx chan".
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      rewrite cancel_prot_unseal.
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iMsg_base_eq.
      iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & (_ & _ & Q))".
      iMod (ghost_var_update_halves false with "γb γb'") as "(γb & γb')".
      iMod (ghost_var_persist with "γb") as "#γb".
      iExists false. iSteps. iExists false. by iSteps.
    + iDecompose "q'" as "chan".
      have -> : ∀ A (b : bool) (a : A) l l', (if b then a :: l else a :: l') = a :: if b then l else l'
        by move=>? [].
      iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
      rewrite cancel_prot_unseal.
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iMsg_base_eq.
      by iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & (% & _))".
  Qed.

  Global Instance recv_or_cancel_recv_spec_continue {TT} c v P Q p :
    SPEC {{ c ↣ <?↯.. (x : TT) | Q > EMSG v x {{ P x }}; p x }}
      recv c
    {{ w, RET w; (∃ tt, ⌜w = SOMEV (v tt)⌝ ∗ c ↣ (p tt) ∗ P tt) ∨
                 (⌜w = NONEV⌝ ∗ cancellable c ∗ Q) }}.
  Proof.
    iSteps as "c". rewrite iProto_pointsto_unseal.
    iDestruct "c" as (γb γf c' γ γ') "(γb & c & γ & #inv)".
    iStep 4.
    iInv "inv" as (q q' ? f) "(>γb' & >γf & chan & >#steps & >#steps' & £ & £')" "close".
    iDestruct (ghost_var_agree with "γb γb'") as %<-.
    iDecompose "chan" as "chan ctx". iFrame "chan".
    iSteps as_anon / as (?) "q' (£1 & £2 & £3)".
    { iExists true. by iSteps. }
    iMod (lc_fupd_elim_later with "£2 ctx") as "ctx".
    case: q'=>[|[m drop] q'].
    + iDecompose "q'" as "γf ctx chan".
      rewrite iProto_dual_message iMsg_dual_exist.
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iMsg_exist_eq.
      iMod (lc_fupd_elim_later with "£1 H") as "(ctx & γ & (%b & H))".
      case: b.
      - iPoseProof (iMsg_dual_involutive (∃.. x : TT, EMSG v x {{ P x }}; p x)%msg with "H") as "H".
        rewrite iMsg_texist_exist iEMsg_base_eq/iEMsg_base_def iMsg_base_eq/iMsg_base_def
          iMsg_exist_eq/=.
        by iDestruct "H" as (???) "(% & _)".
      - iPoseProof (iMsg_dual_base with "H") as "H". rewrite iMsg_base_eq.
        iDestruct "H" as "(_ & eq & Q)". rewrite involutive.
        iPoseProof (later_equivI _ p' with "eq") as "eq".
        iMod (lc_fupd_elim_later with "£3 eq") as "eq".
        iRewrite -"eq" in "γ". iMod (ghost_var_update_halves false with "γb γb'") as "(γb & _)".
        iMod (ghost_var_persist with "γb") as "#γb". iExists false. iSteps. iExists false. by iSteps.
    + iDecompose "q'" as "chan".
      have -> : ∀ A (b : bool) (a : A) l l', (if b then a :: l else a :: l') = a :: if b then l else l'
        by move=>? [].
      iMod (lc_fupd_elim_later with "£1 ctx") as "ctx".
      rewrite iProto_dual_message iMsg_dual_exist.
      iMod (iProto_recv with "ctx γ") as (p') "H".
      rewrite iMsg_exist_eq.
      iMod (lc_fupd_elim_later with "£3 H") as "(ctx & γ & (%b & H))".
      iDestruct "£" as ">(£1 & £)".
      case: b.
      - iPoseProof (iMsg_dual_involutive (∃.. x : TT, EMSG v x {{ P x }}; p x)%msg with "H") as "H".
        rewrite iMsg_texist_exist iEMsg_base_eq/iEMsg_base_def iMsg_base_eq/iMsg_base_def
          iMsg_exist_eq/=.
        iDestruct "H" as (x ??) "(%h & eq & P)". move: h=>[<-->->].
        iDecompose "P" as "(P & _)"/ as "abs"; last by iDestruct (ghost_var_agree with "γb abs") as %abs.
        iPoseProof (later_equivI _ p' with "eq") as "eq".
        iMod (lc_fupd_elim_later with "£1 eq") as "eq".
        iRewrite -"eq" in "γ".
        iExists true. iSteps. iSplitR; last by iSteps.
        iIntros "!>!>". iApply (steps_lb_le with "steps'"). lia.
      - iPoseProof (iMsg_dual_base with "H") as "H". rewrite iMsg_base_eq.
        by iDestruct "H" as "(%abs & _)".
  Qed.

End specs.