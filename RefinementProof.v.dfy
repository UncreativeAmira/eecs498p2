include "RefinementObligation.t.dfy"
//#extract RefinementObligation.t.template inherit RefinementObligation.t.dfy

module RefinementProof refines RefinementObligation {
  import opened IMapHelpers
  import opened MessageType

  ghost function ConstantsAbstraction(c: Constants) : AtomicKVSpec.Constants
  {
/*{*/
    AtomicKVSpec.Constants() //we have no constant
/*}*/
  }

/*{*/
/*}*/

//  _                _      _   _
// | |    ___   ___ | | __ | | | | ___ _ __ ___
// | |   / _ \ / _ \| |/ / | |_| |/ _ \ '__/ _ \
// | |__| (_) | (_) |   <  |  _  |  __/ | |  __/
// |_____\___/ \___/|_|\_\ |_| |_|\___|_|  \___|
//
// Included in this project is a collection of helpful proof tooling.
//
// The informal design intuition for this distributed system is that each key is
// maintained in exactly one place, so we can look at all the components of the
// distributed system and figure out what (total) map it represents. Each
// component of the system knows which key it's responsible for. Hosts can
// transfer responsibility for a key to another host via a network message.
//
// The keys can live either in a host, or -- for brief periods -- in the network
// transfer messages as they fly from one host to another.
//
// Talking about "each key is in exactly one place" can be done by saying "if a
// key is in one host, it's not in another host and not in any message, but also
// if a key is in an in-flight message it's not in any other message and also not
// in any host." But that's a complicated mess. It's cleaner to define an abstract
// notion of a "MapOwner" that owns a partial view of the system, and define it
// for both hosts and messages. Then we can talk about a collection of ALL the
// MapOwners, the partial views they contain, and say "each key is owned by
// exactly one MapOwner."
//
// The first thing this free code gift offers is the PartitionLayer datatype that
// captures this abstract notion of MapOwnership. It encapsulates a map of maps:
// the outer map takes a MapOwner (identifying some host or message) and gives
// back the inner partial key-value map. Dafny's internal map axioms can get
// pretty timeout-y in this situation. The second thing this gift provides is some
// judicious automation control: some {:opaque}d boundaries and "accessor" lemmas
// you can use to interact with the {:opaque}d definitions without revealing them
// in your own proofs. You don't need to reveal anything we've opaqued here, nor
// do you want to, so you can avoid timeouts traps.
//
// So the last question is, what's the proof strategy? For most steps of the
// distributed system, you'll need to show that the spec view corresponds to the
// distributed view. For example, whet the Host Get returns a value, it should
// match the corresponding value in the spec view. And when Put changes a Host's
// state, the spec view should change by the corresponding key:=value update. The
// PartitionLayer helps you make those statements by offering a stepping stone
// between the raw distributed data structures (Host state and Message contents)
// and the Spec View. For example, if you know a Host N maps K to V, you can use
// RawToPartitionEstablishesValue to learn that MapOwner(N) maps K to V in the
// PartitionLayer(c, v) object that represents that raw state.  And if you know
// that fact, you can use PartitionToSpecViewEstablishesValue to learn that the
// aggregate spec view maps K to V, also. Corresponding lemmas let you go the
// opposite direction, "down the stack."
//
// Those helpful transitions only work if we know the MapOwners in the
// PartitionLayer are, in fact, partitioned! That is, every key must be owned by
// some MapOwner (the PartitionLayer must be *full*), and each key must be owned
// by only one MapOwner (the PartitionLayer must be *disjoint*). That's a property
// that your Host protocol should maintain anyway, of course. But that means that
// you need to show that various steps maintain that property. You need to
// establish .IsFullAndDisjoint() for both PartitionLayer(c, v) and
// PartitionLayer(c, v') before you can use the helpful methods above.


  ////////////////////////////////////////////////////////////////////////////
  // Some underlying definitions to support the PartitionLayer datatype

  datatype MapOwner = HostOwner(id: HostId) | MessageOwner(msg: Message)

  // We need a "raw" MapOwner-to-AllPartitions type so we can build a recursive
  // definition for Disjointness.
  type PartitionsByOwner = map<MapOwner, imap<int,int>>

  //////////////////////////////////////////////////////////////////
  // Fullness definitions
  //////////////////////////////////////////////////////////////////

  ghost predicate OwnerDefinesKey(maps: PartitionsByOwner, owner: MapOwner, key: int)
  {
    && owner in maps
    && key in maps[owner]
  }

  ghost predicate SomeOwnerDefinesKey(maps: PartitionsByOwner, key: int)
  {
    exists owner :: OwnerDefinesKey(maps, owner, key)
  }

  // Define "fullness": every key is defined in a map belonging to some owner.
  // (forall-exists puts Dafny in a bad mood, so we break this into separate
  // named definitions.)
  ghost predicate IsFullPartitions(maps: PartitionsByOwner)
  {
    forall key :: SomeOwnerDefinesKey(maps, key)
  }

  //////////////////////////////////////////////////////////////////
  // Disjointness definitions
  //////////////////////////////////////////////////////////////////

  // Dafny's :| should be deterministic (functional), but it ain't.
  ghost function ArbitraryOwner(maps: PartitionsByOwner) : MapOwner
    requires maps != map[]
  {
    var owner :| owner in maps; owner
  }

  ghost function DisjointMapUnion(maps: PartitionsByOwner) : imap<int,int>
  {
    if maps == map[]
    then EmptyMap()
    else
      var source := ArbitraryOwner(maps);
      IMapUnionPreferLeft(DisjointMapUnion(MapRemoveOne(maps, source)), maps[source])
  }

  lemma DisjointMapsDoContainKey(maps: PartitionsByOwner, owner: MapOwner, key:int)
    requires OwnerDefinesKey(maps, owner, key)
    ensures key in DisjointMapUnion(maps)
  {
  }

  lemma DisjointMapsDontContainKey(maps: PartitionsByOwner, key:int)
    requires forall owner :: owner in maps ==> key !in maps[owner]
    ensures key !in DisjointMapUnion(maps)
  {
  }

  ghost predicate {:opaque} IsDisjoint(maps: PartitionsByOwner)
  {
    forall src1, src2
      | src1 in maps && src2 in maps && src1 != src2
      :: maps[src1].Keys !! maps[src2].Keys
  }

  lemma DisjointUnionMapsKeyToValue(maps: PartitionsByOwner, owner: MapOwner, key:int)
    requires IsDisjoint(maps)
    requires owner in maps && key in maps[owner]
    ensures key in DisjointMapUnion(maps)
    ensures DisjointMapUnion(maps)[key] == maps[owner][key]
  {
    reveal_IsDisjoint();
    if maps.Keys != {owner} {
      var someOwner := ArbitraryOwner(maps);
      if owner == someOwner {
        DisjointMapsDontContainKey(MapRemoveOne(maps, someOwner), key);
        assert key !in DisjointMapUnion(MapRemoveOne(maps, someOwner));
      } else {
        DisjointUnionMapsKeyToValue(MapRemoveOne(maps, someOwner), owner, key);
      }
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  //
  // Three layers:
  // Unioned map: one full map<K,V>, used as the abstraction function
  // PartitionLayer: a map of partial maps, indexed by the sum-type MapOwner object,
  //    that we show to be a AllPartitions of the keys, and can use the power of partitioning.
  // Raw representation: the collection of Host tables and inFlightMessages from the
  //    DistributedSystem.

  // Raw layer
  // ---------

  ghost predicate RawOwnerClaimsKey(c: Constants, v: Variables, owner: MapOwner, key: int)
  {
    && v.WF(c)
    && (match owner
      case HostOwner(id) => (
/*{*/
        // this branch should be true if host `id` thinks it owns `key`.
        && c.ValidHostId(id)
        && key in v.hosts[id].hostOwnedMap
/*}*/
      )
      case MessageOwner(msg) => (
/*{*/
        // this branch should be true if in-flight message `msg` thinks it owns `key`.
        //do we have to check for validity of msg? don't think so
        && msg in v.network.inFlightMessages
        && key in msg.sentMap
/*}*/
      )
      )
  }

  ghost predicate RawOwnerAssignsValue(c: Constants, v: Variables, owner: MapOwner, key: int, value: int)
  {
    && RawOwnerClaimsKey(c, v, owner, key)
    && (match owner
      case HostOwner(id) =>
/*{*/
      // this branch should be true if host `id`, which we know claims `key`, assigns it `value`.
      //&& c.ValidHostId(id) not needed, already checked by rawownerclaimskey
      && v.hosts[id].hostOwnedMap[key] == value

        
/*}*/
      case MessageOwner(msg) =>
/*{*/
      // this branch should be true if message `msg` which we know claims `key`, assigns it `value`.
      && msg.sentMap[key] == value
/*}*/
      )
  }

  // PartitionLayer layer
  // A nice abstraction that knows the definition of partitioned (full + disjoint)
  // and can use it to draw useful conclusions.
  // ---------------

  datatype PartitionLayer = PartitionLayer(c: Constants, v: Variables) {

    //////////////////////////////////////////////////////////////////
    // Things you can learn with merely v.WF(c)
    //////////////////////////////////////////////////////////////////

    ghost function ValidHosts() : set<HostId>  // Here to satiate finite-set heuristic
    {
/*{*/
    set id | 0 <= id < |c.hosts| && 0 < |c.hosts| && c.ValidHostId(id) 
/*}*/
    }

    // Build up the AllPartitions() map that talks about *both* host and message ownership

    ghost function HostMaps() : PartitionsByOwner
      requires v.WF(c)
    {
/*{*/
      // Replace with a map whose keys are all of the HostOwners in the system,
      // and the values are the partial maps maintained by each host.
      map id | id in ValidHosts() ::
        HostOwner(id) := v.hosts[id].hostOwnedMap
/*}*/
    }

    ghost function MessageMaps() : PartitionsByOwner
    {
/*{*/
      // Replace with a map whose keys are all of the MessageOwners alive in
      // the system, and the values are the partial maps maintained by each
      // message.
      map msg | msg in v.network.inFlightMessages ::
        MessageOwner(msg) := msg.sentMap
/*}*/
    }

    // This function is defining the desired abstract view: a single map that has
    // everything in it (when this PartitionLayer object is full and disjoint).
    // It crams together everything we learned from the hosts and the in-flight messages
    // into a single map.
    ghost function {:opaque} AllPartitions() : PartitionsByOwner
      requires v.WF(c)
    {
      // The map comprehension in MapUnionPreferLeft seems to lead to timeout grief
      // that's hard to profile, so this is opaque.
      MapUnionPreferLeft(HostMaps(), MessageMaps()) 
    }

    // If we don't touch *anything* in the client tables or network, it's a shame to 
    // do a bunch of work proving VariablesAbstraction() is the same key-by-key. Instead
    // we just peek under the covers and see that AllPartitions() only looks at the
    // tables part of the hosts; changes to DistributedSystem.events don't affect it.
    lemma NoopPreservesSpecView(v': Variables)
      requires IsFullAndDisjoint()
      requires v'.WF(c)
/*{*/
      requires v'.network == v.network // network is unchanged
      requires v'.hosts == v.hosts     //  all hosts' internal state is unchanged
/*}*/
      ensures PartitionLayer(c, v').AllPartitions() == AllPartitions()
    {
      reveal_AllPartitions();
    }

    ghost predicate PartitionOwnerClaimsKey(owner: MapOwner, key: int)
    {
      && v.WF(c)
      && owner in AllPartitions()
      && key in AllPartitions()[owner]
    }

    lemma RawToPartitionClaimsKey(owner: MapOwner, key: int)
      requires RawOwnerClaimsKey(c, v, owner, key)
      ensures PartitionOwnerClaimsKey(owner, key)
    {
      reveal_AllPartitions();
    }

    lemma PartitionToRawClaimsKey(owner: MapOwner, key: int)
      requires PartitionOwnerClaimsKey(owner, key)
      ensures RawOwnerClaimsKey(c, v, owner, key)
    {
      reveal_AllPartitions();
    }

    //////////////////////////////////////////////////////////////////
    // Things you can learn with only map-fullness (every key has at least one
    // owner claiming it)
    //////////////////////////////////////////////////////////////////

    ghost predicate PartitionIsFull() {
      && v.WF(c)
      && IsFullPartitions(AllPartitions())
    }

    lemma GetPartitionOwner(key: int) returns (owner: MapOwner)
      requires PartitionIsFull()
      ensures PartitionOwnerClaimsKey(owner, key)
    {
      assert SomeOwnerDefinesKey(AllPartitions(), key);  // trigger
      var choose_owner :| OwnerDefinesKey(AllPartitions(), choose_owner, key);
      owner := choose_owner;
    }

    //////////////////////////////////////////////////////////////////
    // PartitionLayer.WF() means "this PartitionLayer really partitions the keyspace";
    // it's both full and disjoint.
    // What follows are things you can learn once you know you have a
    // AllPartitions.
    //////////////////////////////////////////////////////////////////

    ghost predicate IsFullAndDisjoint() {
      && v.WF(c)
      && PartitionIsFull()
      && IsDisjoint(AllPartitions())
    }
  
    // Here's a key-granularity definition of disjointness.
    // Prove it to EstablishDisjointness().
    ghost predicate KeysOwnedDisjointly() {
      forall key, owner1, owner2 | PartitionOwnerClaimsKey(owner1, key) && PartitionOwnerClaimsKey(owner2, key) :: owner1 == owner2
    }

    lemma EstablishDisjointness()
      requires PartitionIsFull()
      requires KeysOwnedDisjointly()
      ensures IsFullAndDisjoint()
    {
      var maps := AllPartitions();
      forall owner1, owner2
        | owner1 in maps && owner2 in maps && owner1 != owner2
        ensures maps[owner1].Keys !! maps[owner2].Keys
      {
        forall key ensures !(key in maps[owner1].Keys && key in maps[owner2].Keys) {
          assert key in maps[owner1] ==> PartitionOwnerClaimsKey(owner1, key);
          assert key in maps[owner2] ==> PartitionOwnerClaimsKey(owner2, key);
        }
      }
      reveal_IsDisjoint();
    }

    lemma UseDisjointness()
      requires IsFullAndDisjoint()
      ensures KeysOwnedDisjointly()
    {
      reveal_IsDisjoint();
    }

    lemma SpecViewIsFull()
      requires IsFullAndDisjoint()
      ensures IsFull(DisjointMapUnion(AllPartitions()))
    {
      forall key ensures key in DisjointMapUnion(AllPartitions()) {
        var owner := GetPartitionOwner(key);
        DisjointMapsDoContainKey(AllPartitions(), owner, key);
      }
    }

    // This SpecView() is the "top" layer: the union of all the partitions into one flat k-v map
    // This is the global view, used for the abstraction function.
    ghost function SpecView() : imap<int,int>
      requires IsFullAndDisjoint()
      ensures IsFull(SpecView())
    {
      SpecViewIsFull();
      DisjointMapUnion(AllPartitions())
    }

    ghost predicate OwnerAssignsValue(owner: MapOwner, key: int, value: int)
    {
      && PartitionOwnerClaimsKey(owner, key)
      && AllPartitions()[owner][key] == value
    }

    ghost function Value(key: int) : int
      requires IsFullAndDisjoint()
    {
      SpecView()[key]
    }

    // Need this to show extensionality between two SpecViews.
    // What we'd rather say is "SpecViewHasFullDomain", but I tried to do this by
    // redefining IsFull to say Keys==AllKeys, opaquing both AllKeys and even
    // IsFull, and yet things got real timeoutey real fast. :v(
    lemma SpecViewsAgreeOnDomain(other: PartitionLayer)
      requires IsFullAndDisjoint()
      requires other.IsFullAndDisjoint()
      ensures SpecView().Keys == other.SpecView().Keys
    {
      forall kk ensures kk in SpecView() <==> kk in other.SpecView() {
      }
   }

    lemma PartitionToSpecViewEstablishesValue(owner: MapOwner, key: int, value: int)
      requires IsFullAndDisjoint()
      requires OwnerAssignsValue(owner, key, value)
      ensures Value(key) == value
    {
      DisjointUnionMapsKeyToValue(AllPartitions(), owner, key);
    }

    lemma SpecViewToPartitionEstablishesValue(owner: MapOwner, key: int, value: int)
      requires IsFullAndDisjoint()
      requires PartitionOwnerClaimsKey(owner, key)
      requires Value(key) == value
      ensures OwnerAssignsValue(owner, key, value)
    {
      PartitionToSpecViewEstablishesValue(owner, key, AllPartitions()[owner][key]);
    }

    lemma RawToPartitionEstablishesValue(owner: MapOwner, key: int, value: int)
      requires IsFullAndDisjoint()
      requires RawOwnerAssignsValue(c, v, owner, key, value)
      ensures OwnerAssignsValue(owner, key, value)
    {
      reveal_AllPartitions();
    }

    lemma PartitionToRawEstablishesValue(owner: MapOwner, key: int, value: int)
      requires IsFullAndDisjoint()
      requires OwnerAssignsValue(owner, key, value)
      ensures RawOwnerAssignsValue(c, v, owner, key, value)
    {
      reveal_AllPartitions();
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  ghost function VariablesAbstraction(c: Constants, v: Variables) : AtomicKVSpec.Variables
  {
/*{*/
    // 1. AllPartitions() combines HostMaps() and MessageMaps()
    // 2. DisjointMapUnion() will create single map from all the partitions
    // 3. even if keys overlap, DisjointMapUnion() will still produce map
    // 
    // we'll prove properties about this map thru our invariant
    // 
    // matches AtomicKVSpec's requirements:
    // 1. returns a single imap
    // 2. imap will contain all mappings from hosts to messages
    // 3. properties of this map (like disjointness) will be proven separately in invariant (is this how we do it?)
    // 
    // this is way we can define an abstraction function independently of the properties we'll prove about it
    var allParts := PartitionLayer(c, v).AllPartitions();
    AtomicKVSpec.Variables(DisjointMapUnion(allParts))
/*}*/
  }

/*{*/




lemma InitialStateFull(c: Constants, v: Variables)
  requires c.WF()
  requires v.WF(c)
  requires Init(c, v)
  ensures PartitionLayer(c, v).PartitionIsFull()
{
  
  var pl := PartitionLayer(c, v);
  
  //goes back to the original plan we had but with correct syntax
  //goal: show that when we do .allpartitions for init, despite that being opaque, we will have a full imap
  //def of partitionisfull uses forall key :: SomeOwnerDefinesKey(maps, key)

  forall key 
    ensures SomeOwnerDefinesKey(pl.AllPartitions(), key)
  {
    assert v.hosts[0].hostOwnedMap == ZeroMap();  
    assert IsFull(v.hosts[0].hostOwnedMap); 

    //this is what we didn't know to use originally, connection between raw and others
    assert RawOwnerClaimsKey(c, v, HostOwner(0), key);
    pl.RawToPartitionClaimsKey(HostOwner(0), key);
    assert key in pl.AllPartitions()[HostOwner(0)];
    assert OwnerDefinesKey(pl.AllPartitions(), HostOwner(0), key);
  }
}


lemma InitialStateDisjoint(c: Constants, v: Variables) 
  requires c.WF()
  requires v.WF(c)
  requires Init(c, v)
  ensures PartitionLayer(c, v).KeysOwnedDisjointly()
{
  var pl := PartitionLayer(c, v);
  
  //goal: show that if one owner claims a key, it is unique
  forall key, owner1, owner2 | pl.PartitionOwnerClaimsKey(owner1, key) && pl.PartitionOwnerClaimsKey(owner2, key)
    ensures owner1 == owner2
  {
    pl.PartitionToRawClaimsKey(owner1, key);
    pl.PartitionToRawClaimsKey(owner2, key);
  }
}

lemma IntialStateFullAndDisjoint(c: Constants, v: Variables)
  requires c.WF()
  requires v.WF(c)
  requires Init(c, v)
  ensures PartitionLayer(c, v).IsFullAndDisjoint()
{
  var pl := PartitionLayer(c, v);

  InitialStateFull(c, v);
  InitialStateDisjoint(c, v);
  pl.EstablishDisjointness();
}


lemma InitialStateMatchesSpec(c: Constants, v: Variables)
  requires c.WF()
  requires v.WF(c)
  requires Init(c, v)
  requires PartitionLayer(c, v).IsFullAndDisjoint()
  ensures VariablesAbstraction(c, v).mappy == ZeroMap()
{
  var pl := PartitionLayer(c, v);

  //everything in mappy is in zero map!
  forall key | key in VariablesAbstraction(c, v).mappy.Keys 
    ensures VariablesAbstraction(c, v).mappy[key] == ZeroMap()[key]
  {
    assert v.hosts[0].hostOwnedMap == ZeroMap();
    assert RawOwnerAssignsValue(c, v, HostOwner(0), key, 0);
    
    //again, this is what we didn't use originally: connection from raw to parition to spec
    pl.RawToPartitionEstablishesValue(HostOwner(0), key, 0);
    pl.PartitionToSpecViewEstablishesValue(HostOwner(0), key, 0);
  }
  
  //then everything in zero map is in mappy! 
  forall key | key in ZeroMap().Keys 
    ensures key in VariablesAbstraction(c, v).mappy.Keys && VariablesAbstraction(c, v).mappy[key] == ZeroMap()[key]
  {
    assert v.hosts[0].hostOwnedMap == ZeroMap();
    assert RawOwnerAssignsValue(c, v, HostOwner(0), key, 0);
    pl.RawToPartitionEstablishesValue(HostOwner(0), key, 0);
    pl.PartitionToSpecViewEstablishesValue(HostOwner(0), key, 0);
  }
}


lemma NextPreservesFull(c: Constants, v: Variables, v': Variables, event: Event)
  requires c.WF()
  requires v.WF(c)
  requires v'.WF(c)
  requires Next(c, v, v', event)
  requires PartitionLayer(c, v).IsFullAndDisjoint()  // need old state's properties
  ensures PartitionLayer(c, v').PartitionIsFull()
{
  var pl := PartitionLayer(c, v);
  var pl' := PartitionLayer(c, v');
  var step :| NextStep(c, v, v', event, step);

  forall key ensures SomeOwnerDefinesKey(pl'.AllPartitions(), key) 
  {
    var owner := pl.GetPartitionOwner(key);
    pl.PartitionToRawClaimsKey(owner, key);

    // need to find who owns it in v' - should be same owner or step.hostid or message
    var new_owner := if step.msgOps.send.Some? && key in step.msgOps.send.value.sentMap 
                     then MessageOwner(step.msgOps.send.value)
                     else if step.msgOps.recv.Some? && key in step.msgOps.recv.value.sentMap
                     then HostOwner(step.hostid)
                     else owner;

    assert RawOwnerClaimsKey(c, v', new_owner, key);
    pl'.RawToPartitionClaimsKey(new_owner, key);
    assert key in pl'.AllPartitions()[new_owner];
    assert OwnerDefinesKey(pl'.AllPartitions(), new_owner, key);
  }
}


lemma NextPreservesDisjoint(c: Constants, v: Variables, v': Variables, event: Event)
  requires c.WF()
  requires v.WF(c)
  requires v'.WF(c)
  requires Next(c, v, v', event)
  requires PartitionLayer(c, v).IsFullAndDisjoint()  // need old state's properties
  ensures PartitionLayer(c, v').KeysOwnedDisjointly()
  {
    var pl := PartitionLayer(c, v);
    var pl' := PartitionLayer(c, v');

    forall key, owner1, owner2 | pl'.PartitionOwnerClaimsKey(owner1, key) && pl'.PartitionOwnerClaimsKey(owner2, key)
      ensures owner1 == owner2
    {
      pl'.PartitionToRawClaimsKey(owner1, key);
      pl'.PartitionToRawClaimsKey(owner2, key);
    }
  }

lemma NextStateFullAndDisjoint(c: Constants, v: Variables, v': Variables, event: Event)
  requires c.WF()
  requires v.WF(c)
  requires v'.WF(c)
  requires Next(c, v, v', event)
  requires PartitionLayer(c, v).IsFullAndDisjoint()
  ensures PartitionLayer(c, v').IsFullAndDisjoint()
{
  var pl' := PartitionLayer(c, v');

  NextPreservesFull(c, v, v', event);
  NextPreservesDisjoint(c, v, v', event); 
  pl'.EstablishDisjointness();
}

lemma NextStateMatchesSpec(c: Constants, v: Variables, v': Variables, event: Event)
  requires c.WF()
  requires v.WF(c)
  requires v'.WF(c)
  requires Next(c, v, v', event)
  requires PartitionLayer(c, v).IsFullAndDisjoint()
  requires PartitionLayer(c, v').IsFullAndDisjoint()
  ensures AtomicKVSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
{
  var pl := PartitionLayer(c, v);
  var pl' := PartitionLayer(c, v');
  var step :| NextStep(c, v, v', event, step);

  match event {
    case Get(k, val) => {
      // show value was correctly read
      var owner := pl.GetPartitionOwner(k);
      assert RawOwnerAssignsValue(c, v, owner, k, val);
      pl.RawToPartitionEstablishesValue(owner, k, val);
      pl.PartitionToSpecViewEstablishesValue(owner, k, val);

      // show state unchanged
      forall key | key in VariablesAbstraction(c, v').mappy.Keys
        ensures VariablesAbstraction(c, v').mappy[key] == VariablesAbstraction(c, v).mappy[key]
      {
        var owner := pl.GetPartitionOwner(key);
        var value := pl.Value(key);
        assert RawOwnerAssignsValue(c, v, owner, key, value);
        pl.RawToPartitionEstablishesValue(owner, key, value);
        pl.PartitionToSpecViewEstablishesValue(owner, key, value);
      }
    }

    case Put(k, val) => {
      // show value was correctly updated
      var owner := pl'.GetPartitionOwner(k);
      assert RawOwnerAssignsValue(c, v', owner, k, val);
      pl'.RawToPartitionEstablishesValue(owner, k, val);
      pl'.PartitionToSpecViewEstablishesValue(owner, k, val);

      // show other keys unchanged
      forall key | key in VariablesAbstraction(c, v').mappy.Keys && key != k
        ensures VariablesAbstraction(c, v').mappy[key] == VariablesAbstraction(c, v).mappy[key]
      {
        var owner := pl.GetPartitionOwner(key);
        var value := pl.Value(key);
        assert RawOwnerAssignsValue(c, v, owner, key, value);
        pl.RawToPartitionEstablishesValue(owner, key, value);
        pl.PartitionToSpecViewEstablishesValue(owner, key, value);
      }
    }

    case NoOp => {
      // show all values preserved through transfer
      forall key | key in VariablesAbstraction(c, v').mappy.Keys
        ensures VariablesAbstraction(c, v').mappy[key] == VariablesAbstraction(c, v).mappy[key]
      {
        var owner := pl.GetPartitionOwner(key);
        var value := pl.Value(key);
        
        // track value through potential ownership transfer
        if step.msgOps.send.Some? && key in step.msgOps.send.value.sentMap {
          assert RawOwnerAssignsValue(c, v', MessageOwner(step.msgOps.send.value), key, value);
          pl'.RawToPartitionEstablishesValue(MessageOwner(step.msgOps.send.value), key, value);
          pl'.PartitionToSpecViewEstablishesValue(MessageOwner(step.msgOps.send.value), key, value);
        } 
        else if step.msgOps.recv.Some? && key in step.msgOps.recv.value.sentMap {
          assert RawOwnerAssignsValue(c, v', HostOwner(step.hostid), key, value);
          pl'.RawToPartitionEstablishesValue(HostOwner(step.hostid), key, value);
          pl'.PartitionToSpecViewEstablishesValue(HostOwner(step.hostid), key, value);
        }
        else {
          assert RawOwnerAssignsValue(c, v', owner, key, value);
          pl'.RawToPartitionEstablishesValue(owner, key, value);
          pl'.PartitionToSpecViewEstablishesValue(owner, key, value);
        }
      }
    }
  }
}
/*}*/

  ghost predicate Inv(c: Constants, v: Variables)
  {
/*{*/
    && v.WF(c)
    && c.WF()
    && PartitionLayer(c, v).IsFullAndDisjoint()
/*}*/
  }

  ////////////////////////////////////////////////////////////////////////////


  lemma RefinementInit(c: Constants, v: Variables)
    //requires Init(c, v) // inherited from abstract module
    ensures Inv(c, v)
    ensures AtomicKVSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
  {
/*{*/
    // prove init state fullness (1) and disjointness (2)
    InitialStateFull(c, v);
    InitialStateDisjoint(c, v);
    var pl := PartitionLayer(c, v);

    // full + disjoint work together
    IntialStateFullAndDisjoint(c,v);
    pl.EstablishDisjointness();    

    //actual init connections
    InitialStateMatchesSpec(c, v);
/*}*/
  }

/*{*/
/*}*/

  lemma RefinementNext(c: Constants, v: Variables, v': Variables, event: Event)
    // These requires & ensures all come from RefinementObligations; repeating
    // them here as a nearby crib sheet.
    // requires Next(c, v, v')
    // requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicKVSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
  {
/*{*/
    // prove next state fullness (1) and disjointness (2)
    NextPreservesFull(c, v, v', event);
    NextPreservesDisjoint(c, v, v', event);
    var pl' := PartitionLayer(c, v');

    // full + disjoint work together
    NextStateFullAndDisjoint(c, v, v', event);
    pl'.EstablishDisjointness();

    // actual next connections
    NextStateMatchesSpec(c, v, v', event);
/*}*/
  }
}