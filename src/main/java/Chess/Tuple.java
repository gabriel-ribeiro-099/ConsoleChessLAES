package Chess;

/**
 * Used to store an int/int pair to map to tiles on the chessboard.
 */
/*@
  @ nullable_by_default
  @*/
public class Tuple {

    //@ spec_public
    private final int x;

    //@ spec_public
    private final int y;

    /*@
      @ public invariant x >= 0 && y >= 0;
      @ constraint \old(x) == x && \old(y) == y;
      @*/

    /*@
      @ public normal_behavior
      @     requires x >= 0;
      @     requires y >= 0;
      @     ensures this.x == x;
      @     ensures this.y == y;
      @*/
    public Tuple(int x, int y) {
        //@ assert x >= 0 && y >= 0;
        this.x = x;
        this.y = y;
    }

    /*@
      @ normal_behavior
      @ ensures \result == x;
      @ pure
      @*/
    public int X() {
        return x;
    }

    /*@
      @ normal_behavior
      @ ensures \result == y;
      @ pure
      @*/
    public int Y() {
        return y;
    }
}

