package Chess;

import Chess.ChessPiece.*;
import java.util.ArrayList;

public class ChessGame {

    //@ spec_public
    private final ChessBoard board = new ChessBoard();

    //@ spec_public
    private boolean isFinished = false;

    //@ spec_public
    private PieceColor currentPlayer = PieceColor.White;

    /*@
    @ ensures board != null;
    @ ensures currentPlayer != null;
    @ ensures isFinished == false;
    @*/
    public ChessGame() {
        currentPlayer = PieceColor.White;
        isFinished = false;
    }

    /*@
    @ requires from != null && to != null;
    @ requires isWithinBounds(from) && isWithinBounds(to);
    @ requires board.getTileFromTuple(from) != null;
    @ requires board.getTileFromTuple(to) != null;
    @*/
    public boolean playMove(Tuple from, Tuple to) {
        if (from == null || to == null) {
            throw new IllegalArgumentException("Source or destination tuple cannot be null");
        }
    
        if (!isWithinBounds(from) || !isWithinBounds(to)) {
            return false;
        }
    
        Tile fromTile = board.getTileFromTuple(from);
        if (fromTile == null || fromTile.getPiece() == null) {
            return false;
        }
    
        if (isValidMove(from, to, false)) {
            Tile toTile = board.getTileFromTuple(to);
            //@ assume fromTile.getPiece() != null;
            ChessPiece pieceToMove = fromTile.getPiece();
    
            if (toTile != null) {
                toTile.setPiece(pieceToMove);
                fromTile.empty();
            }
            endTurn();
            return true;
        }
    
        return false;
    }
    

    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public ChessBoard getBoard() {
        return board;
    }

    /*@
      @ ensures \result == isFinished;
      @ pure
      @*/
    public boolean isFinished() {
        return isFinished;
    }

    /*@
      @ assignable currentPlayer;
      @ ensures (currentPlayer == PieceColor.White ==> \old(currentPlayer) == PieceColor.Black) &&
      @         (currentPlayer == PieceColor.Black ==> \old(currentPlayer) == PieceColor.White);
      @*/
    private void endTurn() {
        currentPlayer = (currentPlayer == PieceColor.White)
                ? PieceColor.Black
                : PieceColor.White;
    }

    /*@
    @ requires color != null;
    @ requires (\exists int i; 0 <= i && i < board.getAllPiecesLocationForColor(color).length; 
    @           board.getAllPiecesLocationForColor(color)[i] == null || 
    @           isWithinBounds(board.getAllPiecesLocationForColor(color)[i]));
    @*/
    private boolean isCheckPreventable(PieceColor color) {
        Tuple[] locations = board.getAllPiecesLocationForColor(color);
    
        for (Tuple location : locations) {
    
            if (location == null || !isWithinBounds(location)) {
                continue; 
            }
    
            Tile locationTile = board.getTileFromTuple(location);
            if (locationTile == null || locationTile.getPiece() == null) {
                continue; 
            }
    
            ChessPiece piece = locationTile.getPiece();
    
            Tuple[] possibleMoves = validMovesForPiece(piece, location);
    
            for (Tuple newLocation : possibleMoves) {
    
                if (newLocation != null && !isMoveCausesCheck(color, location, newLocation, piece)) {
                    return true;
                }
            }
        }
        return false; 
    }
    

    

    private boolean isMoveCausesCheck(PieceColor color, Tuple from, Tuple to, ChessPiece piece) {
    
        if (!isWithinBounds(from) || !isWithinBounds(to)) {
            return true; 
        }
    
        Tile toTile = board.getTileFromTuple(to);
        if (toTile == null) {
            return true; 
        }
    
        //@ assume toTile.getPiece() != null;
        ChessPiece toPiece = toTile.getPiece();
    
        boolean causesCheck = true;
    
        try {
            toTile.setPiece(piece); 
            board.getTileFromTuple(from).empty(); 
            causesCheck = isKingCheck(color); 
        } finally {
            board.getTileFromTuple(from).setPiece(piece);
            toTile.setPiece(toPiece);
        }
        return causesCheck;
    }
    
    


    /*@
      @ requires kingColor != null;
      @*/
    protected boolean isKingCheck(PieceColor kingColor) {
        Tuple kingLocation = board.getKingLocation(kingColor);
        if (kingLocation == null || !isWithinBounds(kingLocation)) {
            return false; 
        }
        return canOpponentTakeLocation(kingLocation, kingColor);
    }

    /*@
    @ requires location != null && color != null;
    @ requires isWithinBounds(location);
    @*/
    protected boolean canOpponentTakeLocation(Tuple location, PieceColor color) {
        if (!isWithinBounds(location)) {
            return false;
        }

        PieceColor opponentColor = ChessPiece.opponent(color);
        Tuple[] piecesLocation = board.getAllPiecesLocationForColor(opponentColor);

        for (Tuple fromTuple : piecesLocation) {
            if (fromTuple == null || !isWithinBounds(fromTuple)) {
                continue;
            }

            Tile fromTile = board.getTileFromTuple(fromTuple);
            if (fromTile != null && fromTile.getPiece() != null && 
                isValidMove(fromTuple, location, true)) {
                return true;
            }
        }
        return false;
    }

    

        /*@
    @ requires from != null && to != null;
    @ requires isWithinBounds(from) && isWithinBounds(to);
    @ requires board.getTileFromTuple(from) != null;
    @*/
    protected boolean isValidMove(Tuple from, Tuple to, boolean hypothetical) {
        if (!isWithinBounds(from) || !isWithinBounds(to)) {
            return false;
        }

        Tile fromTile = board.getTileFromTuple(from);
        Tile toTile = board.getTileFromTuple(to);

        //@ assume fromTile.getPiece() != null;
        ChessPiece fromPiece = fromTile.getPiece();

        if (fromPiece.getColor() != currentPlayer || 
            (toTile.getPiece() != null && toTile.getPiece().getColor() == currentPlayer)) {
            return false;
        }

        if (isValidMoveForPiece(from, to)) {
            if (hypothetical) return true;

            //@ assume toTile.getPiece() != null;
            ChessPiece toPiece = toTile.getPiece();
            toTile.setPiece(fromPiece);
            fromTile.empty();

            boolean result = !isKingCheck(currentPlayer);

            fromTile.setPiece(fromPiece);
            toTile.setPiece(toPiece);

            return result;
        }
        return false;
    }

    

    /*@
      @ requires piece != null && currentLocation != null;
      @ ensures \result != null;
      @*/
    private Tuple[] validMovesForPiece(ChessPiece piece, Tuple currentLocation) {
        if (piece.hasRepeatableMoves()) {
            return calculateRepeatableMoves(piece, currentLocation);
        } else {
            return calculateNonRepeatableMoves(piece, currentLocation);
        }
    }

    private Tuple[] calculateRepeatableMoves(ChessPiece piece, Tuple currentLocation) {
        Move[] moves = piece.getMoves();
        ArrayList<Tuple> possibleMoves = new ArrayList<>();
    
        for (Move move : moves) {
            for (int i = 1; i < 8; i++) {
                long tempX = (long) currentLocation.X() + (long) move.x * i;
                long tempY = (long) currentLocation.Y() + (long) move.y * i;
    
                if (tempX >= 0 && tempX < 8 && tempY >= 0 && tempY < 8) {
                    int newX = (int) tempX;
                    int newY = (int) tempY;
    
                    Tuple newLocation = new Tuple(newX, newY); 
                    if (!isWithinBounds(newLocation)) break;
    
                    Tile tile = board.getTileFromTuple(newLocation);
                    if (tile.isEmpty()) {
                        possibleMoves.add(newLocation);
                    } else {
                        if (tile.getPiece().getColor() != piece.getColor()) {
                            possibleMoves.add(newLocation);
                        }
                        break;
                    }
                }
            }
        }
        return possibleMoves.toArray(new Tuple[0]);
    }
    
    private Tuple[] calculateNonRepeatableMoves(ChessPiece piece, Tuple currentLocation) {
        Move[] moves = piece.getMoves();
        ArrayList<Tuple> possibleMoves = new ArrayList<>();
    
        for (Move move : moves) {
            long potentialX = (long) currentLocation.X() + (long) move.x;
            long potentialY = (long) currentLocation.Y() + (long) move.y;
    
            if (potentialX >= 0 && potentialX < 8 && potentialY >= 0 && potentialY < 8) {
                int x = (int) potentialX;
                int y = (int) potentialY;
    
                Tuple newTuple = new Tuple(x, y);
    
                if (!isWithinBounds(newTuple)) {
                    continue;
                }
    
                Tile tile = board.getTileFromTuple(newTuple);
                if (tile == null || tile.isEmpty() || tile.getPiece().getColor() != piece.getColor()) {
                    possibleMoves.add(newTuple);
                }
            }
        }
    
        return possibleMoves.toArray(new Tuple[0]);
    }
    
    

    private boolean isValidMoveForPiece(Tuple from, Tuple to) {
        Tile fromTile = board.getTileFromTuple(from);
    
        //@ assume fromTile.getPiece() != null;
        ChessPiece fromPiece = fromTile.getPiece();
    
        if (fromPiece.hasRepeatableMoves()) {
            return isValidMoveForPieceRepeatable(from, to);
        } else {
            return isValidMoveForPieceNonRepeatable(from, to);
        }
    }
    

    private boolean isValidMoveForPieceRepeatable(Tuple from, Tuple to) {
        Tile fromTile = board.getTileFromTuple(from);
    
        //@ assume fromTile.getPiece() != null;
        ChessPiece fromPiece = fromTile.getPiece();
    
        Move[] moves = fromPiece.getMoves();
    
        for (int i = 1; i < 8; i++) {
            for (Move move : moves) {
    
                long potentialX = (long) from.X() + (long) move.x * i;
                long potentialY = (long) from.Y() + (long) move.y * i;
    
                if (potentialX >= 0 && potentialX < 8 && potentialY >= 0 && potentialY < 8) {
                    int newX = (int) potentialX;
                    int newY = (int) potentialY;
    
                    Tuple newLocation = new Tuple(newX, newY);
    
                    if (newX == to.X() && newY == to.Y()) {
                        return true;
                    }
    
                    Tile newLocationTile = board.getTileFromTuple(newLocation);
    
                    if (!isWithinBounds(newLocation) || !newLocationTile.isEmpty()) {
                        break;
                    }
                }
            }
        }
        return false;
    }
    

    private boolean isValidMoveForPieceNonRepeatable(Tuple from, Tuple to) {
        ChessPiece fromPiece = board.getTileFromTuple(from).getPiece();
        Move[] moves = fromPiece.getMoves();

        for (Move move : moves) {
            long potentialX = (long) from.X() + (long) move.x;
            long potentialY = (long) from.Y() + (long) move.y;

            if (potentialX >= 0 && potentialX < 8 && potentialY >= 0 && potentialY < 8) {
                int newX = (int) potentialX;
                int newY = (int) potentialY;

            if (newX == to.X() && newY == to.Y()) {
                return true;
            }
        }}
        return false;
    }

    /*@
      @ requires tuple != null;
      @ ensures \result == (tuple.X() >= 0 && tuple.X() < 8 && tuple.Y() >= 0 && tuple.Y() < 8);
      @ pure
      @*/
    public boolean isWithinBounds(Tuple tuple) {
        return tuple.X() >= 0 && tuple.X() < 8 && tuple.Y() >= 0 && tuple.Y() < 8;
    }

}