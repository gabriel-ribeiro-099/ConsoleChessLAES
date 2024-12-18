package Chess;
import Chess.Pieces.*;
import java.util.ArrayList;

public class ChessBoard {
    /*@ public invariant board != null && board.length == 8 &&
    @ (\forall int i; 0 <= i && i < 8; board[i] != null && board[i].length == 8);
    @ initially board != null;
    @*/    

    //@ spec_public
    private final Tile[][] board;

    /*@ 
    @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
    @*/
    public ChessBoard() {
        board = new Tile[8][8];
        initializeBoard();
        fillBoard();
    }

    //@ pure
    public Tile[][] getBoardArray() {
        return board;
    }

    /*@
    @ requires board != null;
    @ requires board.length == 8;
    @ requires (\forall int i; 0 <= i && i < 8; board[i] != null && board[i].length == 8);
    @ ensures (\forall int i; 0 <= i && i < 8;
    @            (\forall int j; 0 <= j && j < 8; board[i][j] != null));
    @*/
    private void initializeBoard() {
        //@ maintaining 0 <= i && i <= 8;
        //@ maintaining (\forall int k; 0 <= k && k < i; (\forall int l; 0 <= l && l < 8; board[k][l] != null));
        //@ decreases 8 - i;
        //@ loop_writes board[0..7][0..7];
        for (int i = 0; i < 8; i++) {
            //@ maintaining 0 <= j && j <= 8;
            //@ maintaining (\forall int l; 0 <= l && l < j; board[i][l] != null);
            //@ decreases 8 - j;
            //@ loop_writes board[i][0..7];
            for (int j = 0; j < 8; j++) {
                Tile tile = ((i + j) % 2 == 0)
                    ? new Tile(Tile.TileColor.Black)
                    : new Tile(Tile.TileColor.White);
                //@ assert tile != null;
                board[i][j] = tile;
                //@ assert board[i][j] != null;
            }
            //@ assert \forall int j; 0 <= j && j < 8; board[i][j] != null;
        }
    }



    /*@
    @ requires (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
    @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j].getPiece() != null || board[i][j].getPiece() == null);
    @*/
    private void fillBoard() {
        //@ maintaining 0 <= i && i <= 8;
        //@ decreases 8 - i;
        for (int i = 0; i < 8; i++) {
            board[1][i].setPiece(new Pawn(ChessPiece.PieceColor.Black));
            board[6][i].setPiece(new Pawn(ChessPiece.PieceColor.White));
        }

        // Rooks
        board[0][0].setPiece(new Rook(ChessPiece.PieceColor.Black));
        board[0][7].setPiece(new Rook(ChessPiece.PieceColor.Black));
        board[7][0].setPiece(new Rook(ChessPiece.PieceColor.White));
        board[7][7].setPiece(new Rook(ChessPiece.PieceColor.White));

        // Knights
        board[0][1].setPiece(new Knight(ChessPiece.PieceColor.Black));
        board[0][6].setPiece(new Knight(ChessPiece.PieceColor.Black));
        board[7][1].setPiece(new Knight(ChessPiece.PieceColor.White));
        board[7][6].setPiece(new Knight(ChessPiece.PieceColor.White));

        // Bishops
        board[0][2].setPiece(new Bishop(ChessPiece.PieceColor.Black));
        board[0][5].setPiece(new Bishop(ChessPiece.PieceColor.Black));
        board[7][2].setPiece(new Bishop(ChessPiece.PieceColor.White));
        board[7][5].setPiece(new Bishop(ChessPiece.PieceColor.White));

        // Queens
        board[0][3].setPiece(new Queen(ChessPiece.PieceColor.Black));
        board[7][3].setPiece(new Queen(ChessPiece.PieceColor.White));

        // Kings
        board[0][4].setPiece(new King(ChessPiece.PieceColor.Black));
        board[7][4].setPiece(new King(ChessPiece.PieceColor.White));
    }



    /*@
    @ requires color != null;
    @ ensures \result != null;
    @ pure
    @*/
    public Tuple[] getAllPiecesLocationForColor(ChessPiece.PieceColor color) {
        ArrayList<Tuple> locations = new ArrayList<>();
        //@ loop_invariant 0 <= x && x <= 8;
        for (int x = 0; x < 8; x++) {
            //@ loop_invariant 0 <= y && y <= 8;
            for (int y = 0; y < 8; y++) {
                //@ assume board[y][x] != null;
                if (!board[y][x].isEmpty() && board[y][x].getPiece().getColor() == color) {
                    Tuple t = new Tuple(x, y);
                    locations.add(t);
                }
            }
        }
        return locations.toArray(new Tuple[0]);
    }

    /*@
    @ requires color != null;
    @ ensures \result != null;
    @*/
    public Tuple getKingLocation(ChessPiece.PieceColor color) {
        //@ loop_invariant 0 <= x && x <= 8;
        for (int x = 0; x < 8; x++) {
            //@ loop_invariant 0 <= y && y <= 8;
            for (int y = 0; y < 8; y++) {
                //@ assume board[y][x] != null;
                if (!board[y][x].isEmpty() && board[y][x].getPiece() instanceof King && board[y][x].getPiece().getColor() == color) {
                    return new Tuple(x, y);
                }
            }
        }
        return new Tuple(0, 0); 
    }

    /*@
    @ requires tuple != null;
    @ ensures \result != null;
    @ pure
    @*/
    public Tile getTileFromTuple(Tuple tuple) {
        if (tuple == null || tuple.X() < 0 || tuple.X() >= 8 || tuple.Y() < 0 || tuple.Y() >= 8) {
            throw new IllegalArgumentException("Tuple is out of bounds");
        }
        //@ assume board[tuple.Y()][tuple.X()] != null;
        return board[tuple.Y()][tuple.X()];
    }
}
