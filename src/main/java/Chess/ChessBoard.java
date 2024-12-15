package Chess;
import Chess.Pieces.*;
import java.util.ArrayList;

public class ChessBoard {
    /*@ public invariant board != null && board.length == 8 &&
    @ (\forall int i; 0 <= i && i < 8; board[i] != null && board[i].length == 8);
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


    public Tile[][] getBoardArray() {
        return board;
    }

    /*@
    @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
    @*/
    private void initializeBoard() {
        //@ loop_invariant 0 <= i && i <= 8;
        for (int i = 0; i < 8; i++) {
            //@ loop_invariant 0 <= j && j <= 8;
            for (int j = 0; j < 8; j++) {
                //@ assume 0 <= i && i < 8 && 0 <= j && j < 8; 
                Tile tile = ((i + j) % 2 == 0)
                ? new Tile(Tile.TileColor.Black)
                : new Tile(Tile.TileColor.White);
                //@ assume tile != null;
                board[i][j] = tile;
                //@ assume board[i][j] != null;
            }
        }
    }

    /*@
    @ requires (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
    @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j].getPiece() != null || board[i][j].getPiece() == null);
    @*/
    private void fillBoard() {
        //@ loop_invariant 0 <= i && i <= 8;
        for (int i = 0; i < 8; i++) {
            //@ assume 0 <= i && i < 8;
            board[1][i].setPiece(new Pawn(ChessPiece.PieceColor.Black));
            board[6][i].setPiece(new Pawn(ChessPiece.PieceColor.White));
        }

        // Rooks
        //@ assume board[0][0] != null;
        board[0][0].setPiece(new Rook(ChessPiece.PieceColor.Black));
        //@ assume board[0][7] != null;
        board[0][7].setPiece(new Rook(ChessPiece.PieceColor.Black));
        //@ assume board[7][0] != null;
        board[7][0].setPiece(new Rook(ChessPiece.PieceColor.White));
        //@ assume board[7][7] != null;
        board[7][7].setPiece(new Rook(ChessPiece.PieceColor.White));

        // Knights
        //@ assume board[0][1] != null;
        board[0][1].setPiece(new Knight(ChessPiece.PieceColor.Black));
        //@ assume board[0][6] != null;
        board[0][6].setPiece(new Knight(ChessPiece.PieceColor.Black));
        //@ assume board[7][1] != null;
        board[7][1].setPiece(new Knight(ChessPiece.PieceColor.White));
        //@ assume board[7][6] != null;
        board[7][6].setPiece(new Knight(ChessPiece.PieceColor.White));

        // Bishops
        //@ assume board[0][2] != null;
        board[0][2].setPiece(new Bishop(ChessPiece.PieceColor.Black));
        //@ assume board[0][5] != null;
        board[0][5].setPiece(new Bishop(ChessPiece.PieceColor.Black));
        //@ assume board[7][2] != null;
        board[7][2].setPiece(new Bishop(ChessPiece.PieceColor.White));
        //@ assume board[7][5] != null;
        board[7][5].setPiece(new Bishop(ChessPiece.PieceColor.White));

        // Queens
        //@ assume board[0][3] != null;
        board[0][3].setPiece(new Queen(ChessPiece.PieceColor.Black));
        //@ assume board[7][3] != null;
        board[7][3].setPiece(new Queen(ChessPiece.PieceColor.White));

        // Kings
        //@ assume board[0][4] != null;
        board[0][4].setPiece(new King(ChessPiece.PieceColor.Black));
        //@ assume board[7][4] != null;
        board[7][4].setPiece(new King(ChessPiece.PieceColor.White));
    }

    public Tuple[] getAllPiecesLocationForColor(ChessPiece.PieceColor color) {
        //@ assume (\forall int y, x; 0 <= y && y < 8 && 0 <= x && x < 8; board[y][x] != null);
        ArrayList<Tuple> locations = new ArrayList<>();
        //@ loop_invariant 0 <= x && x <= 8;
        for (int x = 0; x < 8; x++) {
            //@ loop_invariant 0 <= y && y <= 8;
            for (int y = 0; y < 8; y++) {
                //@ assume 0 <= x && x < 8 && 0 <= y && y < 8;
                //@ assume board[y][x] != null;
                if (!board[y][x].isEmpty() && board[y][x].getPiece().getColor() == color) {
                    Tuple t = new Tuple(x, y);
                    //@ assume t != null;
                    //@ assume locations.size() >= 0;
                    locations.add(t);
                }
            }
        }
        return locations.toArray(new Tuple[0]);
    }

    public Tuple getKingLocation(ChessPiece.PieceColor color) {
        //@ loop_invariant 0 <= x && x <= 8;
        for (int x = 0; x < 8; x++) {
            //@ loop_invariant 0 <= y && y <= 8;
            for (int y = 0; y < 8; y++) {
                //@ assume 0 <= x && x < 8 && 0 <= y && y < 8;
                //@ assume board[y][x] != null;
                if (!board[y][x].isEmpty() && board[y][x].getPiece() instanceof King && board[y][x].getPiece().getColor() == color) {
                    //@ assume 0 <= x && x < 8 && 0 <= y && y < 8;
                    return new Tuple(x, y);
                }
            }
        }
        return new Tuple(0, 0); 
    }

    /*@
    @ requires tuple != null;
    @ requires 0 <= tuple.Y() && tuple.Y() < 8;
    @ requires 0 <= tuple.X() && tuple.X() < 8;
    @ ensures \result != null;
    @*/
    public Tile getTileFromTuple(Tuple tuple) {
        //@ assume tuple != null;
        //@ assume board[tuple.Y()][tuple.X()] != null;
        return board[tuple.Y()][tuple.X()];
    }
}
