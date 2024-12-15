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
      @ constraint \old(x) == x && \old(y) == y;
      @*/

    /*@
      @ requires (x >= 0 && y >= 0 && x < 8 && y < 8) || (x == -1 && y == -1);
      @ ensures this.x == x;
      @ ensures this.y == y;
      @ pure
      @*/
    public Tuple(int x, int y) {
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

