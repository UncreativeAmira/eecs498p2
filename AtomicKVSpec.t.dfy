module AtomicKVSpec {
  import opened IMapHelpers
  import opened Types

  datatype Constants = Constants()  // don't need any here
  datatype Variables = Variables(
  /*{*/
  mappy: imap <int, int>
  /*}*/
  )

  // The initial map should assign the value zero to every key.
  // Be sure to check out IMapHelpers.t.dfy. It's helpful.
  ghost predicate Init(c: Constants, v: Variables) {
  /*{*/
    && v.mappy == ZeroMap()
  /*}*/
  }

  /*{*/
  /*}*/

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event) {
  /*{*/
  match event {
    case Get(key, value) =>
      && key in v.mappy
      && value == v.mappy[key]
      && v' == v
      
    case Put(key, value) =>
      && v'.mappy == v.mappy[key := value]
      
    case NoOp() =>
      && v' == v
  }
  /*}*/
}

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    // All the nondeterminism is encoded in `event`! No `exists` required.
    NextStep(c, v, v', event)
  }
}
