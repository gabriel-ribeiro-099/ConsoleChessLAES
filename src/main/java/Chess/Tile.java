package Chess;

/*@ nullable_by_default @*/
public class Tile {

    //@ spec_public
    private ChessPiece piece;

    //@ spec_public
    private final TileColor color;


    /*@
    @ public invariant piece == null || piece instanceof ChessPiece;
    @ invariant TileColor.White != null;
    @ invariant TileColor.Black != null;
    @ pure
    @*/
    public enum TileColor{
        White, Black
    }

    /*@ 
    @ requires color != null;
    @ requires color == TileColor.Black || color == TileColor.White; 
    @ ensures this.color == color;
    @*/
    public Tile(TileColor color){
        this.color = color;
    }

    /*@ 
    @ requires color != null;
    @ ensures color == this.color;
    @ ensures piece == this.piece;
    @ pure
    @*/
    public Tile(TileColor color, ChessPiece piece){
        this.color = color;
        //@ assume piece == null || piece instanceof ChessPiece;
        this.piece = piece;
    }

    /*@ 
    @ normal_behavior
    @   requires piece != null;
    @   ensures this.piece == piece;
    @*/
    public void setPiece(ChessPiece piece){
        this.piece = piece;
    }

    /*@ 
    @ normal_behavior
    @ ensures \result == this.piece;
    @ ensures \result == null || \result instanceof ChessPiece;
    @ pure
    @*/
    public ChessPiece getPiece(){
        return this.piece;
    }

    /*@
    @ normal_behavior
    @ ensures piece != null ==> \result.equals("[" + piece.getCharValue() + "]");
    @ ensures piece == null ==> \result.equals("[ ]");
    @ pure
    @*/
    public String getValue() {
        if (piece != null) {
            return "[" + piece.getCharValue() + "]";
        } else {
            return "[ ]";
        }
    }


    /*@ 
    @ ensures \result == (piece == null);
    @*/
    public boolean isEmpty(){
        return piece == null;
    }

    /*@ 
    @ ensures piece == null;
    @ assignable piece;
    @*/
    public void empty(){
        piece = null;
    }
}
