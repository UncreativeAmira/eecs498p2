include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy
include "MessageType.v.dfy"
//#extract MessageType.v.template inherit MessageType.v.dfy
include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy

//
// Your protocol should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKVSpec, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//
// Initially host 0 should own all the keys.
//
// Don't forget about the helper functions in IMapHelpers.t.dfy. They can be
// quite useful!

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

/*{*/
  // Replace these definitions with more meaningful ones that capture the operations
  // of a key-value store described above.
  datatype Constants = Constants() 
  datatype Variables = Variables(hostOwnedMap: imap <int, int>)


  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && |grp_v| > 0 // Not sure if we need this, but keeping in for my paranioa 
    && forall idx | 0 <= idx < |grp_v| :: grp_v[idx].hostOwnedMap == if idx == 0 then ZeroMap() else EmptyMap() //is zero map correct here?
  }

  ghost predicate SendMessage(c: Constants, v: Variables, v': Variables, event: Event, msgOps:Network.MessageOps) {
    && msgOps.send.Some? 
    && msgOps.recv.None? 
    && var keySet := msgOps.send.value.sentMap.Keys; //set of keys needed for the remove
    && (forall k :: (k) in msgOps.send.value.sentMap ==> (k in v.hostOwnedMap) && msgOps.send.value.sentMap[k] == v.hostOwnedMap[k]) //need some way to check that we have what we are sending!!!
    && v'.hostOwnedMap == MapRemove(v.hostOwnedMap, keySet) //and then remove it from 
  } 


  ghost predicate ReceiveMessage(c: Constants, v: Variables, v': Variables, event: Event, msgOps: Network.MessageOps) {
    && msgOps.send.None? 
    && msgOps.recv.Some? 
    && v'.hostOwnedMap == IMapUnionPreferLeft(msgOps.recv.value.sentMap, v.hostOwnedMap) //just take it in
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event, msgOps: Network.MessageOps)
    {
      match event {
      case Get(key, value) =>
        && key in v.hostOwnedMap
        && value == v.hostOwnedMap[key]
        && v' == v
    
      case Put(key, value) =>
        && v'.hostOwnedMap == v.hostOwnedMap[key := value]
        
      case NoOp => SendMessage(c, v, v', event, msgOps) || ReceiveMessage(c, v, v', event, msgOps)

      }
    }

/*}*/
}
