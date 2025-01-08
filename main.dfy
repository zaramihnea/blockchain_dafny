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

}

class Block{
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
        hashAttempts > 0
    }

    constructor(time: int, tran: seq<Transaction>, prevHash: string)
        requires time > 0
        requires |tran| > 0
        requires |prevHash| > 0
        ensures timestamp == time
        ensures transactions == tran
        ensures previousHash == prevHash
    {
        timestamp := time;
        transactions := tran;
        previousHash := prevHash;
        hashAttempts := 0;
        hash := "initial";
    }

    method Mine(difficulty: int) returns (success: bool)
        requires Valid()
        requires difficulty >0
        modifies this
        ensures Valid()
    {
        hashAttempts := hashAttempts + 1;
        //hashing implementation Sha-256 :)
        hash := "mined hash";
        success := true;
    }

}

class Blockchain{
    var chain: seq<Block>

    predicate Valid()
        reads this
    {
        |chain| >0 
    }

    constructor()
        ensures Valid()
        ensures |chain| == 1
    {
        var firstTransaction := new Transaction("first", "first", 1);
        var firstBlock := new Block(1, [firstTransaction], "0");
        chain := [firstBlock];
    }

    method AddBlock(newBlock: Block) returns (success: bool)
        requires Valid()
        requires newBlock != null && newBlock.Valid()
        ensures Valid()
    {
        var lenght := |chain|;
        if newBlock.previousHash == chain[lenght - 1].hash {
            chain := chain + [newBlock];
            success := true;
        } else {
            success := false;
        }
    }

}

method Main(){

}