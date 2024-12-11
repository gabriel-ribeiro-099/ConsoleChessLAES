package Chess;

import Chess.Pieces.*;

import java.util.ArrayList;

public class ChessBoard {
    //@ spec_public
    private final Tile[][] board;

    /*@ public invariant board != null && board.length == 8 && board[0].length == 8;
      @ public invariant (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
      @*/

    /*@ public normal_behavior
      @     ensures board.length == 8 && board[0].length == 8;
      @     ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
      @*/
    public ChessBoard() {
        board = new Tile[8][8];
        initializeBoard();
        fillBoard();
    }

    /*@ public normal_behavior
      @ ensures board.length == 8 && board[0].length == 8;
      @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
      @ pure
      @*/
    public Tile[][] getBoardArray() {
        return board;
    }

    /*@ private normal_behavior
      @ ensures (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8; board[i][j] != null);
      @*/
    private void initializeBoard() {
        //@ loop_invariant 0 <= i && i <= 8;
        //@ loop_invariant (\forall int k, j; 0 <= k && k < i && 0 <= j && j < 8; board[k][j] != null);
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
                if ((i + j) % 2 == 0) {
                    board[i][j] = new Tile(Tile.TileColor.Black);
                } else {
                    board[i][j] = new Tile(Tile.TileColor.White);
                }
            }
        }
    }

    /*@ private normal_behavior
      @ requires board != null && board.length == 8 && board[0].length == 8;
      @ ensures (\forall int i; 0 <= i && i < 8; 
      @            board[1][i].getPiece() instanceof Pawn && 
      @            board[6][i].getPiece() instanceof Pawn);
      @ ensures board[0][0].getPiece() instanceof Rook && board[0][7].getPiece() instanceof Rook;
      @ ensures board[7][0].getPiece() instanceof Rook && board[7][7].getPiece() instanceof Rook;
      @ ensures board[0][1].getPiece() instanceof Knight && board[0][6].getPiece() instanceof Knight;
      @ ensures board[7][1].getPiece() instanceof Knight && board[7][6].getPiece() instanceof Knight;
      @ ensures board[0][2].getPiece() instanceof Bishop && board[0][5].getPiece() instanceof Bishop;
      @ ensures board[7][2].getPiece() instanceof Bishop && board[7][5].getPiece() instanceof Bishop;
      @ ensures board[0][3].getPiece() instanceof Queen && board[7][3].getPiece() instanceof Queen;
      @ ensures board[0][4].getPiece() instanceof King && board[7][4].getPiece() instanceof King;
      @ assignable board[*][*];
      @*/
    private void fillBoard() {
        //@ loop_invariant 0 <= i && i <= 8;
        //@ loop_invariant (\forall int k; 0 <= k && k < i; board[1][k].getPiece() instanceof Pawn && board[6][k].getPiece() instanceof Pawn);
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

    /*@ public normal_behavior
      @ requires color != null;
      @ ensures \result != null && \result.getPiece() instanceof King && \result.getPiece().getColor() == color;
      @ assignable \nothing;
      @*/
    public Tuple getKingLocation(ChessPiece.PieceColor color) {
        for (int x = 0; x < 8; x++) {
            for (int y = 0; y < 8; y++) {
                if (!board[y][x].isEmpty() && board[y][x].getPiece() instanceof King && board[y][x].getPiece().getColor() == color) {
                    return new Tuple(x, y);
                }
            }
        }
        return new Tuple(-1, -1); // Default invalid position if not found.
    }

    /*@ public normal_behavior
      @ requires color != null;
      @ ensures (\forall int i; 0 <= i && i < \result.length; 
      @             board[\result[i].Y()][\result[i].X()].getPiece().getColor() == color);
      @ assignable \nothing;
      @*/
    public Tuple[] getAllPiecesLocationForColor(ChessPiece.PieceColor color) {
        ArrayList<Tuple> locations = new ArrayList<>();
        for (int x = 0; x < 8; x++) {
            for (int y = 0; y < 8; y++) {
                if (!board[y][x].isEmpty() && board[y][x].getPiece().getColor() == color) {
                    locations.add(new Tuple(x, y));
                }
            }
        }
        return locations.toArray(new Tuple[0]);
    }

    /*@ public normal_behavior
      @ requires tuple != null;
      @ ensures \result != null && \result == board[tuple.Y()][tuple.X()];
      @ pure
      @*/
    public Tile getTileFromTuple(Tuple tuple) {
        return board[tuple.Y()][tuple.X()];
    }
}
