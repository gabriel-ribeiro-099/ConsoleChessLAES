package Chess;

/**
 * Used to store an int/int pair to map to tiles on the chessboard.
 */
public class Tuple {
    //@ spec_public
    private final int x;
    //@ spec_public
    private final int y;

    /*@ public normal_behavior
      @     requires x >= 0;
      @     requires y >= 0;
      @     ensures this.x == x;
      @     ensures this.y == y;
      @*/

    public Tuple(int x, int y){
            this.x = x;
            this.y =y;
    }

    public int X(){
        return x;
    }

    public int Y(){
        return y;
    }

}
