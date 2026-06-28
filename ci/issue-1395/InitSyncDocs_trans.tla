---- MODULE InitSyncDocs_trans ----
EXTENDS Sequences, Naturals, Integers, FiniteSets
CONSTANTS Document, Key, Nil, EOF
(*--algorithm InitSyncDocs
variables oplog = <<>>, remoteColl \in [Document -> {Nil} \cup DocumentVal], remoteCollSeq \in {remoteCollSeq0 \in [1..Cardinality({d \in DOMAIN remoteColl : remoteColl[d] # Nil}) -> {d \in DOMAIN remoteColl : remoteColl[d] # Nil}] : Injective(remoteCollSeq0)}, cursor = 1, localColl = [d \in Document |-> Nil], syncing = TRUE;
define
    Range(f) == {f[i] : i \in DOMAIN f}
    Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y
    DeleteElement(seq, index) == [i \in 1..(Len(seq)-1) |-> IF i<index THEN seq[i] ELSE seq[(i+1)]]
    CloneComplete == (cursor = EOF)
    DocumentVal == [Key -> {0, Nil}]
    DataConsistency == (syncing = FALSE /\ oplog = <<>>) => (remoteColl = localColl)
    InsertExistingDocDuringClone == /\ syncing = TRUE
    /\ ~CloneComplete
    \* The next document to fetch is 'd', but 'd' already exists locally.
    /\ \E d \in Document:
        /\ Len(remoteCollSeq) > 0
        /\ cursor <= Len(remoteCollSeq)
        /\ remoteCollSeq[cursor] = d /\ localColl[d] # Nil

\* A state predicate that holds true when the next step we take would be to apply an update operation
\* to a document that doesn't exist locally.

    ApplyUpdateToMissingDoc == /\ Len(oplog) > 0
    /\ syncing = FALSE
    /\ Head(oplog)[1] = "u" \* about to apply an insert.
    /\ LET d == Head(oplog)[2] IN localColl[d] = Nil


end define;
begin
    Loop:
        while TRUE do
            either
                with d \in Document, dv \in DocumentVal do
                    await syncing;
                    await remoteColl[d] = Nil;
                    remoteColl := [remoteColl EXCEPT ![d] = dv];
                    remoteCollSeq := Append(remoteCollSeq, d);
                    oplog := Append(oplog, <<"i", d, Nil, dv>>);
                end with;
            or
                with d \in Document do
                    await syncing;
                    await remoteColl[d] # Nil;
                    remoteColl := [remoteColl EXCEPT ![d] = Nil];
                    oplog := Append(oplog, <<"d", d, Nil, Nil>>);
                    with ind = CHOOSE i \in DOMAIN remoteCollSeq : remoteCollSeq[i] = d do
                        remoteCollSeq := DeleteElement(remoteCollSeq, ind);
                        cursor := IF cursor = EOF THEN cursor ELSE
                    IF cursor > ind THEN (cursor - 1) ELSE cursor;
                    end with;
                end with;
            or
                with d \in Document, k \in Key do
                    await syncing;
                    await remoteColl[d] # Nil;
                    with newVersion = IF remoteColl[d][k] = Nil THEN 0 ELSE remoteColl[d][k] + 1 do
                        remoteColl := [remoteColl EXCEPT ![d] = [remoteColl[d] EXCEPT ![k] = newVersion]];
                        oplog := Append(oplog, <<"u", d, k, newVersion>>);
                    end with;
                end with;
            or
                await ~CloneComplete;
                await cursor <= Len(remoteCollSeq);
                with d = remoteCollSeq[cursor] do
                    localColl := [localColl EXCEPT ![d] = remoteColl[d]];
                    cursor := IF (cursor + 1) > Len(remoteCollSeq) THEN EOF ELSE (cursor + 1);
                end with;
            or
                await CloneComplete;
                await syncing = TRUE;
                syncing := FALSE;
            or
                await syncing = FALSE;
                await Len(oplog) > 0;
                with op = Head(oplog)[1], d = Head(oplog)[2], k = Head(oplog)[3], v = Head(oplog)[4] do
                    if op = "i" then
                        localColl := [localColl EXCEPT ![d] = v];
                    else
                        if op = "u" then
                            localColl := [localColl EXCEPT ![d] =
                    IF localColl[d] = Nil
                    \* The document doesn't exist locally. Create it with the single key value. (i.e. an "upsert").
                    THEN [ik \in Key |-> IF ik = k THEN v ELSE Nil]
                    \* The document exists locally and we update the key.
                    ELSE [localColl[d] EXCEPT ![k] = v]];
                        else
                            if op = "d" then
                                localColl := [localColl EXCEPT ![d] = Nil];
                            end if;
                        end if;
                    end if;
                end with;
                oplog := Tail(oplog);
            end either;
        end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f246ec11" /\ chksum(tla) = "5e512bae")
VARIABLES oplog, remoteColl, remoteCollSeq, cursor, localColl, syncing

(* define statement *)
Range(f) == {f[i] : i \in DOMAIN f}
Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y
DeleteElement(seq, index) == [i \in 1..(Len(seq)-1) |-> IF i<index THEN seq[i] ELSE seq[(i+1)]]
CloneComplete == (cursor = EOF)
DocumentVal == [Key -> {0, Nil}]
DataConsistency == (syncing = FALSE /\ oplog = <<>>) => (remoteColl = localColl)
InsertExistingDocDuringClone == /\ syncing = TRUE
/\ ~CloneComplete

/\ \E d \in Document:
    /\ Len(remoteCollSeq) > 0
    /\ cursor <= Len(remoteCollSeq)
    /\ remoteCollSeq[cursor] = d /\ localColl[d] # Nil




ApplyUpdateToMissingDoc == /\ Len(oplog) > 0
/\ syncing = FALSE
/\ Head(oplog)[1] = "u"
/\ LET d == Head(oplog)[2] IN localColl[d] = Nil


vars == << oplog, remoteColl, remoteCollSeq, cursor, localColl, syncing >>

Init == (* Global variables *)
        /\ oplog = <<>>
        /\ remoteColl \in [Document -> {Nil} \cup DocumentVal]
        /\ remoteCollSeq \in {remoteCollSeq0 \in [1..Cardinality({d \in DOMAIN remoteColl : remoteColl[d] # Nil}) -> {d \in DOMAIN remoteColl : remoteColl[d] # Nil}] : Injective(remoteCollSeq0)}
        /\ cursor = 1
        /\ localColl = [d \in Document |-> Nil]
        /\ syncing = TRUE

Next == \/ /\ \E d \in Document:
                \E dv \in DocumentVal:
                  /\ syncing
                  /\ remoteColl[d] = Nil
                  /\ remoteColl' = [remoteColl EXCEPT ![d] = dv]
                  /\ remoteCollSeq' = Append(remoteCollSeq, d)
                  /\ oplog' = Append(oplog, <<"i", d, Nil, dv>>)
           /\ UNCHANGED <<cursor, localColl, syncing>>
        \/ /\ \E d \in Document:
                /\ syncing
                /\ remoteColl[d] # Nil
                /\ remoteColl' = [remoteColl EXCEPT ![d] = Nil]
                /\ oplog' = Append(oplog, <<"d", d, Nil, Nil>>)
                /\ LET ind == CHOOSE i \in DOMAIN remoteCollSeq : remoteCollSeq[i] = d IN
                     /\ remoteCollSeq' = DeleteElement(remoteCollSeq, ind)
                     /\ cursor' = (              IF cursor = EOF THEN cursor ELSE
                                   IF cursor > ind THEN (cursor - 1) ELSE cursor)
           /\ UNCHANGED <<localColl, syncing>>
        \/ /\ \E d \in Document:
                \E k \in Key:
                  /\ syncing
                  /\ remoteColl[d] # Nil
                  /\ LET newVersion == IF remoteColl[d][k] = Nil THEN 0 ELSE remoteColl[d][k] + 1 IN
                       /\ remoteColl' = [remoteColl EXCEPT ![d] = [remoteColl[d] EXCEPT ![k] = newVersion]]
                       /\ oplog' = Append(oplog, <<"u", d, k, newVersion>>)
           /\ UNCHANGED <<remoteCollSeq, cursor, localColl, syncing>>
        \/ /\ ~CloneComplete
           /\ cursor <= Len(remoteCollSeq)
           /\ LET d == remoteCollSeq[cursor] IN
                /\ localColl' = [localColl EXCEPT ![d] = remoteColl[d]]
                /\ cursor' = (IF (cursor + 1) > Len(remoteCollSeq) THEN EOF ELSE (cursor + 1))
           /\ UNCHANGED <<oplog, remoteColl, remoteCollSeq, syncing>>
        \/ /\ CloneComplete
           /\ syncing = TRUE
           /\ syncing' = FALSE
           /\ UNCHANGED <<oplog, remoteColl, remoteCollSeq, cursor, localColl>>
        \/ /\ syncing = FALSE
           /\ Len(oplog) > 0
           /\ LET op == Head(oplog)[1] IN
                LET d == Head(oplog)[2] IN
                  LET k == Head(oplog)[3] IN
                    LET v == Head(oplog)[4] IN
                      IF op = "i"
                         THEN /\ localColl' = [localColl EXCEPT ![d] = v]
                         ELSE /\ IF op = "u"
                                    THEN /\ localColl' =                      [localColl EXCEPT ![d] =
                                                         IF localColl[d] = Nil

                                                         THEN [ik \in Key |-> IF ik = k THEN v ELSE Nil]

                                                         ELSE [localColl[d] EXCEPT ![k] = v]]
                                    ELSE /\ IF op = "d"
                                               THEN /\ localColl' = [localColl EXCEPT ![d] = Nil]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED localColl
           /\ oplog' = Tail(oplog)
           /\ UNCHANGED <<remoteColl, remoteCollSeq, cursor, syncing>>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

====
