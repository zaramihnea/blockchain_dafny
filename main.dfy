class Transaction{
  var sender: string
  var destination: string
  var amount: int

  constructor(s: string, d: string, a: int)
    requires a > 0
    ensures sender == sender
    ensures sender == s && destination == d && amount == a
  {
    sender := s;
    destination := d;
    amount := a;
  }
  method PrintTransaction()
    ensures true
  {
    print "    Transaction:\n";
    print "      Sender: ";
    print sender;
    print "\n      Destination: ";
    print destination;
    print "\n      Amount: ";
    print amount;
    print "\n";
  }
}

class Block {
  var timestamp: int
  var transactions: seq<Transaction>
  var previousHash: string
  var hash: string
  var hashAttempts: int

  predicate Valid()
    reads this
  {
    timestamp > 0 &&
    |previousHash| > 0 &&
    |hash| > 0 &&
    hashAttempts >= 0
  }

  constructor(time: int, tran: seq<Transaction>, prevHash: string)
    requires time > 0
    requires |tran| > 0
    requires |prevHash| > 0
    ensures timestamp == time
    ensures transactions == tran
    ensures previousHash == prevHash
    ensures hash == "initial" || hash == "genesisHash"
    ensures hashAttempts == 0
  {
    timestamp := time;
    transactions := tran;
    previousHash := prevHash;
    hashAttempts := 0;
    hash := "initial";
  }

  method Mine(difficulty: int) returns (success: bool)
    requires Valid()
    requires difficulty > 0
    modifies this
    ensures Valid()
  {
    hashAttempts := hashAttempts + 1;
    hash := "mined_hash";
    success := true;
  }

  method PrintBlock()
    ensures true
  {
    print "Block:\n";
    print "  Timestamp: ";
    print timestamp;
    print "\n  Previous Hash: ";
    print previousHash;
    print "\n  Hash: ";
    print hash;
    print "\n  Transactions:\n";

    var i: int := 0;
    while i < |transactions|
      invariant 0 <= i <= |transactions|
    {
      transactions[i].PrintTransaction();
      i := i + 1;
    }
    print "\n";
  }

}

class Blockchain {
  var chain: seq<Block>

  predicate Valid()
    reads this, chain, chain[..]
    reads this
  {
    |chain| > 0 &&
    forall i :: 0 <= i < |chain| ==> |chain[i].hash| > 0
  }

  constructor()
    ensures Valid()
    ensures |chain| == 1
    ensures chain[0].hash == "genesisHash"
  {
    var firstTransaction := new Transaction("first", "first", 1);
    var firstBlock := new Block(1, [firstTransaction], "0");
    firstBlock.hash := "genesisHash";
    chain := [firstBlock];
    assert |firstBlock.hash| > 0;
  }

  method AddBlock(newBlock: Block) returns (success: bool)
    requires Valid()
    requires newBlock.Valid()
    modifies this
    ensures Valid()
  {
    var length := |chain|;
    if newBlock.previousHash == chain[length - 1].hash {
      chain := chain + [newBlock];
      success := true;
    } else {
      success := false;
    }
  }

  method PrintBlockchain()
    ensures true
  {
    print "Blockchain:\n";

    var i: int := 0;
    while i < |chain|
      invariant 0 <= i <= |chain|
    {
      chain[i].PrintBlock();
      i := i + 1;
    }
    print "End of Blockchain\n";
  }

}

method Main() {
  var blockchain := new Blockchain();

  assert blockchain.chain[0].hash == "genesisHash";

  // === PRIMUL BLOC ADĂUGAT DUPĂ GENESIS ===
  var transaction1 := new Transaction("Alice", "Bob", 50);

  if |blockchain.chain| > 0 {
    var previousHash := blockchain.chain[|blockchain.chain| - 1].hash;
    assert |previousHash| > 0;

    var newBlock := new Block(2, [transaction1], previousHash);
    assert newBlock.hashAttempts == 0;
    assert newBlock.Valid();

    var mined := newBlock.Mine(2);
    if mined {
      var success := blockchain.AddBlock(newBlock);
      if success {
        print "Block #1 added successfully.\n";
      } else {
        print "Failed to add block #1.\n";
      }
    } else {
      print "Mining for block #1 failed.\n";
    }
  }

  // === AL DOILEA BLOC ===
  var transaction3 := new Transaction("Charlie", "Dave", 75);

  if |blockchain.chain| > 0 {
    var previousHash2 := blockchain.chain[|blockchain.chain| - 1].hash;
    assert |previousHash2| > 0;

    var newBlock2 := new Block(3, [transaction3], previousHash2);
    assert newBlock2.hashAttempts == 0;
    assert newBlock2.Valid();

    var mined2 := newBlock2.Mine(2);
    if mined2 {
      var success2 := blockchain.AddBlock(newBlock2);
      if success2 {
        print "Block #2 added successfully.\n";
      } else {
        print "Failed to add block #2.\n";
      }
    } else {
      print "Mining for block #2 failed.\n";
    }
  }

  // === AL TREILEA BLOC ===
  var transaction5 := new Transaction("Alice", "Frank", 20);

  if |blockchain.chain| > 0 {
    var previousHash3 := blockchain.chain[|blockchain.chain| - 1].hash;
    assert |previousHash3| > 0;

    var newBlock3 := new Block(4, [transaction5], previousHash3);
    assert newBlock3.hashAttempts == 0;
    assert newBlock3.Valid();

    var mined3 := newBlock3.Mine(2);
    if mined3 {
      var success3 := blockchain.AddBlock(newBlock3);
      if success3 {
        print "Block #3 added successfully.\n";
      } else {
        print "Failed to add block #3.\n";
      }
    } else {
      print "Mining for block #3 failed.\n";
    }
  }

  if blockchain.Valid() {
    print "Blockchain is valid.\n";
  } else {
    print "Blockchain is invalid.\n";
  }

  blockchain.PrintBlockchain();
}