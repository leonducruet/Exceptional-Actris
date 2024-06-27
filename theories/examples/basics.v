From diaframe.heap_lang Require Import proof_automation.
From eactris.utils Require Import ghost_var.
From eactris Require Import channel.

Definition unit_drop : val := λ: <>, #().

Definition pointer_drop l : val := λ: <>, Free l.

Definition assert : val := λ: "b", if: "b" then #() else #() #().

Definition cancel_send : val :=
  λ: <>,
  let: "p" := new_chan #() in
  let: "c" := Fst "p" in
  let: "c'" := Snd "p" in
  Fork (send "c" #42 unit_drop;; cancel "c");;
  let: "r1" := recv "c'" in
  let: "r2" := recv "c'" in
  assert (("r1" = SOMEV #42) && ("r2" = NONEV)).

Definition send_both : val :=
  λ: <>,
  let: "p" := new_chan #() in
  let: "c" := Fst "p" in
  let: "c'" := Snd "p" in
  Fork (send "c" #42 unit_drop;;
        let: "ret" := recv "c" in assert ("ret" = SOMEV #true));;
  send "c'" #true unit_drop;;
  let: "ret" := recv "c'" in assert ("ret" = SOMEV #42).

Definition server : val :=
  λ: "c" "secret",
  let: "key" := recv "c" in
  if: "secret" = "key" then
    let: "data" := recv "c" in
    "data" <- #true;;
    send "c" #() unit_drop
  else
    cancel "c".

Definition client : val :=
  λ: "c" "try",
  let: "data" := ref #() in
  send "c" "try" unit_drop;;
  send "c" "data" (λ: <>, "data" <- #false);;
  recv "c";;
  !"data".

Definition main_succ : val :=
  λ: <>,
  let: "p" := new_chan #() in
  let: "c" := Fst "p" in
  let: "c'" := Snd "p" in
  Fork (server "c" #42);;
  client "c'" #42.

Section proofs.

  Context `{heapGS Σ, chanG Σ, ghost_varG Σ bool}.

  Definition inv_def γ data : iProp Σ :=
    ∃ v, data ↦ v ∗
      (⌜v = #()⌝ ∨ ∃ b : bool, ⌜v = #b⌝ ∗ γ ↪ b).

  Definition client_prot : iProto Σ :=
    <! (key : Z)> EMSG #key; <! γ l> EMSG #l {{ inv nroot (inv_def γ l) }};

  Lemma server_spec (c : val) (secret : Z) :
    {{ c ↣ 













