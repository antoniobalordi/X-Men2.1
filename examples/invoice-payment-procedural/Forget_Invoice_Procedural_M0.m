/****MODEL****/
theory InvoiceProcedural

begin

builtins: asymmetric-encryption, signing, symmetric-encryption

/* PROCEDURAL-FORGETTING VARIANT of examples/invoice-payment (paper, Sec. "The
   ceremony under procedural forgetting").  As in the paper's role scripts, S
   encrypts all its messages to H under the shared key kSH, and the setup
   message carries the service and the amount as well as the account
   (Fig. 12).  When the account-change notice arrives, H forgets how to
   decrypt with a symmetric key: ForgetRule('r_sdec') in H_2.

   Secure channels.  S -> H: S's messages reach H alone and H can rely on
   them.  H <-> B: H has logged in to the bank's application, so H and B are
   mutually authenticated; the messages keep the paper's signatures and
   encryption.  Each message is delivered once (linear Sec fact).  The
   channel fact SndS(A,B,label,values) carries the sender and receiver, so
   the paper's <S,H,acc> and <S,H,svc,amt> are sent as acc and <svc,amt>. */
rule ChanSndS:
	[ SndS($A,$B,xt,x) ]
	--[ ChanSndS($A,$B,xt,x) ]->
	[ Sec($A,$B,xt,x) ]

rule ChanRcvS:
	[ Sec($A,$B,xt,x) ]
	--[ ChanRcvS($A,$B,xt,x) ]->
	[ RcvS($A,$B,xt,x) ]

/****RULES****/

rule humansetup:
[ Fr(~ltkH)
, Fr(~ltkB)
, Fr(~accOld)
, Fr(~accNew)
, Fr(~svc)
, Fr(~amt)
, Fr(~kSH)
]
--[ OnlyOnce()
, Neq($S,$Human)
, Neq($S,$B)
, Neq($Human,$B)
, Neq(~accOld,~accNew)
]->
[ !Type($S,'agentname',$S)
, !Type($Human,'agentname',$Human)
, !Type($B,'agentname',$B)
, !Type($Human,'account',~accOld)
, !Type($Human,'account',~accNew)
, !Type($Human,'service',~svc)
, !Type($Human,'amount',~amt)
, !Ltk($Human,~ltkH)
, !Pk($Human,pk(~ltkH))
, !Ltk($B,~ltkB)
, !Pk($B,pk(~ltkB))
, !Invoice($S,$Human,$B,~accOld,~accNew,~svc,~amt,~kSH)
, Out(pk(~ltkH))
, Out(pk(~ltkB))
]

rule Setup:
[ !Invoice($S,$Human,$B,accOld,accNew,svc,amt,kSH)
, !Ltk($Human,ltkH)
, !Ltk($B,ltkB)
]
--[ Setup($Human)
, Roles($S,$Human,$B)
]->
[ State($S,'1',<$Human,accOld,accNew,svc,amt,kSH>)
, State($Human,'1',<$S,$B,ltkH,kSH>)
, State($B,'1',<$Human,ltkB>)
]

rule S_1:
[ State($S,'1',<$Human,accOld,accNew,svc,amt,kSH>)
]
--[ Send($S,'n1',accOld)
, To($Human)
, Nominate($S,$Human,accOld)
, S_Nominate($S,accOld)
]->
[ State($S,'2',<$Human,accOld,accNew,svc,amt,kSH>)
, SndS($S,$Human,<'n1'>,<senc(<'Setup',svc,amt,accOld>,kSH)>)
]

rule S_2:
[ State($S,'2',<$Human,accOld,accNew,svc,amt,kSH>)
]
--[ Send($S,'n2',accNew)
, To($Human)
, Nominate($S,$Human,accNew)
, S_Nominate($S,accNew)
, LostAccess($S,accOld)
]->
[ State($S,'3',<$Human,accOld,accNew,svc,amt,kSH>)
, SndS($S,$Human,<'n2'>,<senc(<'AccountChange',accNew>,kSH)>)
]

rule S_3:
[ State($S,'3',<$Human,accOld,accNew,svc,amt,kSH>)
]
--[ Send($S,'n3',<svc,amt>)
, To($Human)
, Reminder($S,$Human,svc,amt)
]->
[ State($S,'4',<$Human,accOld,accNew,svc,amt,kSH>)
, SndS($S,$Human,<'n3'>,<senc(<'Reminder',svc,amt>,kSH)>)
]

rule H_1:
[ State($Human,'1',<$S,$B,ltkH,kSH>)
, RcvS($S,$Human,<'n1'>,<senc(<'Setup',svc,amt,accOld>,kSH)>)
]
--[ H()
, Receive($Human,'n1',accOld)
, RecordAccount($Human,$S,accOld)
]->
[ State($Human,'2',<$S,$B,ltkH,kSH,svc,amt,accOld>)
]

rule H_2_M:
[ State($Human,'2',<$S,$B,ltkH,kSH,svc,amt,accOld>)
, RcvS($S,$Human,<'n2'>,<senc(<'AccountChange',accNew>,kSH)>)
]
--[ H()
, Receive($Human,'n2',senc(<'AccountChange',accNew>,kSH))
]->
[ State($Human,'3',<$S,$B,ltkH,kSH,svc,amt,accOld,accNew>)
]

rule H_3_M:
[ State($Human,'3',<$S,$B,ltkH,kSH,svc,amt,accOld,accNew>)
, RcvS($S,$Human,<'n3'>,<senc(<'Reminder',svc,amt>,kSH)>)
, !Pk($B,pkB)
]
--[ H()
, Receive($Human,'n3',senc(<'Reminder',svc,amt>,kSH))
, Send($Human,'o1',aenc(<<$Human,$B,$S,svc,amt,accOld>,sign(<$Human,$B,$S,svc,amt,accOld>,ltkH)>,pkB))
, To($B)
, PaymentOrder($Human,$B,$S,svc,amt,accOld)
]->
[ State($Human,'4',<$S,$B,ltkH,kSH,accOld,accNew,svc,amt>)
, SndS($Human,$B,<'order'>,<aenc(<<$Human,$B,$S,svc,amt,accOld>,sign(<$Human,$B,$S,svc,amt,accOld>,ltkH)>,pkB)>)
]

rule H_4_M:
[ State($Human,'4',<$S,$B,ltkH,kSH,accOld,accNew,svc,amt>)
, !Pk($B,pkB)
, RcvS($B,$Human,<'approval'>,<aenc(<<'Approve',$B,$Human,order>,sigB>,pk(ltkH))>)
]
--[ H()
, Receive($Human,'a1',<'Approve',$B,$Human,order>)
, Eq(verify(sigB,<'Approve',$B,$Human,order>,pkB),true)
, CheckApproval(order,<$Human,$B,$S,svc,amt,accOld>)
, WarningShown($Human,$B)
, Confirmed($Human,$B,$S,svc,amt,accOld)
, H_Confirm($Human,$B,$S,svc,amt,accOld)
, Send($Human,'c1',aenc(<<'Confirm',$Human,$B,order>,sign(<'Confirm',$Human,$B,order>,ltkH)>,pkB))
, To($B)
]->
[ State($Human,'5',<$S,$B,ltkH,kSH,accOld,accOld,svc,amt>)
, SndS($Human,$B,<'confirmation'>,<aenc(<<'Confirm',$Human,$B,order>,sign(<'Confirm',$Human,$B,order>,ltkH)>,pkB)>)
]

rule H_5:
[ State($Human,'5',<$S,$B,ltkH,kSH,accOld,accNew,svc,amt>)
, RcvS($B,$Human,<'status'>,<'PaymentExecuted'>)
]
--[ H()
, Hfin($Human,'PaymentExecuted')
, PaymentSuccess($Human,$B)
]->
[ 
]

rule Bank_1:
[ State($B,'1',<$Human,ltkB>)
, !Pk($Human,pkH)
, RcvS($Human,$B,<'order'>,<aenc(<<$Human,$B,s,svc,amt,acc>,sigH>,pk(ltkB))>)
]
--[ Receive($B,'o1',<$Human,$B,s,svc,amt,acc>)
, Eq(verify(sigH,<$Human,$B,s,svc,amt,acc>,pkH),true)
, CheckOrder($B,$Human,s,svc,amt,acc)
]->
[ State($B,'2',<$Human,ltkB,pkH,s,svc,amt,acc>)
, SndS($B,$Human,<'approval'>,<aenc(<<'Approve',$B,$Human,<$Human,$B,s,svc,amt,acc>>,sign(<'Approve',$B,$Human,<$Human,$B,s,svc,amt,acc>>,ltkB)>,pkH)>)
]

rule Bank_2:
[ State($B,'2',<$Human,ltkB,pkH,s,svc,amt,acc>)
, RcvS($Human,$B,<'confirmation'>,<aenc(<<'Confirm',$Human,$B,<$Human,$B,s,svc,amt,acc>>,sigC>,pk(ltkB))>)
]
--[ Receive($B,'c1',<'Confirm',$Human,$B,<$Human,$B,s,svc,amt,acc>>)
, Eq(verify(sigC,<'Confirm',$Human,$B,<$Human,$B,s,svc,amt,acc>>,pkH),true)
, CheckConf($B,$Human,s,svc,amt,acc)
, TransferDetail($B,$Human,s,svc,amt,acc)
, Transfer(amt,acc)
]->
[ SndS($B,$Human,<'status'>,<'PaymentExecuted'>)
]


/****ENDOFRULES****/

/****RESTRICTIONS****/

restriction OnlyOnce:
	"All #i #j. OnlyOnce()@#i & OnlyOnce()@#j ==> #i = #j"

/* One ceremony: a single session of S, H and B. */
restriction OneSession:
	"All h1 h2 #i #j. Setup(h1) @ #i & Setup(h2) @ #j ==> #i = #j"

restriction Inequality:
	"All x #i. Neq(x,x) @ #i ==> F"

restriction Equality:
	"All x y #i. Eq(x,y) @ #i ==> x = y"

/* CheckApproval (H): the approved order is the order H expects. */
restriction CheckApproval:
	"All x y #i. CheckApproval(x,y) @ #i ==> x = y"

restriction notSameRole:
	"All S H B #i. Roles(S,H,B) @ i ==>
		  not S = H
		& not S = B
		& not H = B"

/****LEMMAS****/

/* [SG3] -- paper Listing 3.  Should HOLD, also in the mutated ceremony. */
lemma Transfer_as_confirmed: all-traces
"All amt acc #i.
    Transfer(amt, acc) @ #i
    ==> (Ex h b s srv #j.
         H_Confirm(h, b, s, srv, amt, acc) @ #j
         & #j < #i)"

/* [SG4] -- paper Listing 4.  Violated by the Forget mutation. */
lemma Transfer_to_latest_account: all-traces
"All amt acc #i.
    Transfer(amt, acc) @ #i
    ==> (Ex s #j.
         S_Nominate(s, acc) @ #j
         & #j < #i
         & not (Ex acc2 #k.
                S_Nominate(s, acc2) @ #k
                & #j < #k & #k < #i))"

/* SECURITY GOAL — violated by the forget mutation.
   After a payment reminder, the money is paid into the account that S
   most recently nominated before that reminder.
   Tamarin should find a counterexample in the mutated ceremony. */
lemma Payment_To_Latest_Nominated_Account: all-traces
	"All b h s svc amt acc #t.
	   TransferDetail(b,h,s,svc,amt,acc) @ #t
	   ==> Ex #n #r. Nominate(s,h,acc) @ #n
	       & Reminder(s,h,svc,amt) @ #r
	       & #n < #r & #r < #t
	       & not (Ex acc2 #n2. Nominate(s,h,acc2) @ #n2 & #n < #n2 & #n2 < #r)"

/* SECURITY GOAL — violated by the forget mutation.
   The money is never paid into an account S can no longer use. */
lemma Payment_Not_Into_Lost_Account: all-traces
	"All b h s svc amt acc #t #l.
	   TransferDetail(b,h,s,svc,amt,acc) @ #t & LostAccess(s,acc) @ #l & #l < #t
	   ==> F"

/* BANK BEHAVES AS SPECIFIED — should HOLD, also in the mutated ceremony.
   B transfers only what its authenticated customer has ordered and then
   explicitly confirmed after seeing the warning. */
lemma Transfer_Requires_Confirmation: all-traces
	"All b h s svc amt acc #t.
	   TransferDetail(b,h,s,svc,amt,acc) @ #t
	   ==> Ex #o #c. PaymentOrder(h,b,s,svc,amt,acc) @ #o
	       & WarningShown(h,b) @ #c
	       & Confirmed(h,b,s,svc,amt,acc) @ #c
	       & #o < #c & #c < #t"

/* ATTACK WITNESS — exists-trace.
   The forget mutation alone (no attacker, no compromised key) makes B
   transfer the reminded amount into accOld after S nominated accNew. */
lemma Lapse_Pays_Old_Account: exists-trace
	"Ex b h s svc amt accOld accNew #n1 #n2 #r #t.
	   Nominate(s,h,accOld) @ #n1
	 & Nominate(s,h,accNew) @ #n2
	 & Reminder(s,h,svc,amt) @ #r
	 & TransferDetail(b,h,s,svc,amt,accOld) @ #t
	 & #n1 < #n2 & #n2 < #r & #r < #t
	 & not accOld = accNew"

/* FUNCTIONAL — a confirmed payment is executed and reported to H. */
lemma Functional: exists-trace
	"Ex b h s svc amt acc #t #i.
	   TransferDetail(b,h,s,svc,amt,acc) @ #t
	 & PaymentSuccess(h,b) @ #i
	 & #t < #i"

end

/****ENDOFMODEL****/