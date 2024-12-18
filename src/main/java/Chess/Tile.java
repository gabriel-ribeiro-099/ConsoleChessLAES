package Chess;

/*@ nullable_by_default @*/
public class Tile {

    //@ spec_public
    private ChessPiece piece; // ou algum valor padrão válido

    //@ spec_public
    private final TileColor color;

    /*@
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
    @ requires piece == null || piece instanceof ChessPiece;
    @ ensures this.piece == piece;
    @ assignable this.piece;
    @*/
    public void setPiece(ChessPiece piece){
        //@ assume piece == null || piece instanceof ChessPiece;
        this.piece = piece;
    }


    /*@
    @ ensures \result == null || \result instanceof ChessPiece;
    @ ensures \result == null ==> this.piece == null;
    @ ensures \result != null ==> this.piece != null && \result == this.piece;
    @ pure
    @*/
    public ChessPiece getPiece() {
        //@ assert this.piece == null || this.piece instanceof ChessPiece;
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
    @ pure
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
