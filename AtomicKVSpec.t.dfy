include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy

// The application spec for this system is a key-value store
// that maintains a map of int keys to int values.
// The type of the state in this state machine is simply a total imap: one in
// which every possible key is in the domain.
// The user-visible actions are Get and Put operations.
// Get accepts a key and returns a value.
// Put accepts a key and a value and returns nothing.
//
// You should write a synchronous spec that produces the world-visible
// events defined in Types.t.dfy: Get and Put (plus NoOp).

module AtomicKVSpec {
  import opened IMapHelpers
  import opened Types

  datatype Constants = Constants()  // don't need any here
  datatype Variables = Variables(
  /*{*/
  key: int, 
  value: int, 
  mappy: imap <int, int>
  /*}*/
  )

  // The initial map should assign the value zero to every key.
  // Be sure to check out IMapHelpers.t.dfy. It's helpful.
  ghost predicate Init(c: Constants, v: Variables) {
  /*{*/
    && forall k :: IsKey(k) ==> (k in v.mappy && v.mappy[k] == 0) //check that its a key, check that it's in mappy, and then check that it's 0
  /*}*/
  }

  /*{*/

  ghost predicate Get(c: Constants, v: Variables, v':Variables, givenKey: int, returnValue: int)
  {
    && IsKey(givenKey)           
    && givenKey in v.mappy       
    && returnValue == v.mappy[givenKey] 
    && v' == v
  }

  ghost predicate Put(c: Constants, v: Variables, v': Variables, givenKey:int, givenValue:int){
    && IsKey(givenKey)
    && v'.mappy == v.mappy[givenKey := givenValue] 
    && (forall k :: k != givenKey ==> (k in v.mappy <==> k in v'.mappy)) 
    && (forall k :: k != givenKey ==> (k in v.mappy ==> v.mappy[k] == v'.mappy[k])) 
  }

  ghost predicate NoOp(c: Constants, v: Variables, v': Variables){
    && v' == v
  }

  /*}*/

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event) {
  /*{*/
    | Get(c, v, v', event.key, event.value)
    | Put(c, v, v', event.key, event.value)
    | NoOp(c, v, v', event)
  /*}*/
}

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    // All the nondeterminism is encoded in `event`! No `exists` required.
    NextStep(c, v, v', event)
  }
}
