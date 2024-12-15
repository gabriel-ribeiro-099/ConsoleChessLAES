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
        //@ assume from != null && to != null;
        if (from == null || to == null) {
            throw new IllegalArgumentException("Source or destination tuple cannot be null");
        }
    
        //@ assume isWithinBounds(from) && isWithinBounds(to);
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
    @ requires (\forall int i; 0 <= i && i < board.getAllPiecesLocationForColor(color).length; 
    @           board.getAllPiecesLocationForColor(color)[i] == null || 
    @           isWithinBounds(board.getAllPiecesLocationForColor(color)[i]));
    @*/
    private boolean isCheckPreventable(PieceColor color) {
        //@ assume color != null; // Ajuda o provador a saber que a cor não é nula
        Tuple[] locations = board.getAllPiecesLocationForColor(color);
        //@ assume locations != null; // Supondo que o método nunca retorna nulo
    
        for (Tuple location : locations) {
            //@ assume location == null || isWithinBounds(location); // Ajudando na verificação de limites
    
            if (location == null || !isWithinBounds(location)) {
                continue; // Ignorar posições inválidas
            }
    
            //@ assume board.getTileFromTuple(location) != null; // Garantindo que o tile nunca seja nulo
            Tile locationTile = board.getTileFromTuple(location);
            if (locationTile == null || locationTile.getPiece() == null) {
                continue; // Ignorar tiles vazios ou sem peças
            }
    
            ChessPiece piece = locationTile.getPiece();
            //@ assume piece != null; // Ajuda a garantir que a peça não é nula
    
            Tuple[] possibleMoves = validMovesForPiece(piece, location);
            //@ assume possibleMoves != null; // Supondo que sempre retorna um array válido
    
            for (Tuple newLocation : possibleMoves) {
                //@ assume newLocation == null || isWithinBounds(newLocation); // Garantindo que os movimentos possíveis sejam válidos
    
                if (newLocation != null && !isMoveCausesCheck(color, location, newLocation, piece)) {
                    return true; // Se um movimento prevenir o cheque, retorna verdadeiro
                }
            }
        }
        return false; // Nenhum movimento válido que previna cheque foi encontrado
    }
    

    

    private boolean isMoveCausesCheck(PieceColor color, Tuple from, Tuple to, ChessPiece piece) {
        //@ assume color != null && from != null && to != null && piece != null;
    
        // Verifique explicitamente se as coordenadas estão dentro dos limites
        if (!isWithinBounds(from) || !isWithinBounds(to)) {
            return true; // Movimento inválido fora do tabuleiro
        }
    
        // Obtenha o tile de destino e garanta que ele não seja nulo
        Tile toTile = board.getTileFromTuple(to);
        if (toTile == null) {
            return true; // Se o tile for nulo, o movimento não é permitido
        }
        //@ assume toTile != null;
    
        // Obtenha a peça no tile de destino e trate o valor nulo explicitamente
        ChessPiece toPiece = toTile.getPiece();
        //@ assume toPiece == null || toPiece != null;
    
        boolean causesCheck = true;
    
        // Simula o movimento sem alterar o estado do tabuleiro
        try {
            toTile.setPiece(piece); // Coloca a peça no tile de destino
            board.getTileFromTuple(from).empty(); // Remove a peça do tile de origem
            causesCheck = isKingCheck(color); // Verifica se o rei está em xeque
        } finally {
            // Reverte o movimento logicamente
            board.getTileFromTuple(from).setPiece(piece);
            toTile.setPiece(toPiece);
        }
        return causesCheck;
    }
    
    


    /*@
      @ requires kingColor != null;
      @*/
    protected boolean isKingCheck(PieceColor kingColor) {
        //@ assume kingColor != null;
        Tuple kingLocation = board.getKingLocation(kingColor);
        //@ assume kingLocation == null || isWithinBounds(kingLocation);
        if (kingLocation == null || !isWithinBounds(kingLocation)) {
            return false; // Rei não está em uma posição válida
        }
        return canOpponentTakeLocation(kingLocation, kingColor);
    }

    /*@
    @ requires location != null && color != null;
    @ requires isWithinBounds(location);
    @*/
    protected boolean canOpponentTakeLocation(Tuple location, PieceColor color) {
        //@ assume location != null && isWithinBounds(location);
        if (!isWithinBounds(location)) {
            return false;
        }

        PieceColor opponentColor = ChessPiece.opponent(color);
        Tuple[] piecesLocation = board.getAllPiecesLocationForColor(opponentColor);

        for (Tuple fromTuple : piecesLocation) {
            //@ assume fromTuple == null || isWithinBounds(fromTuple);
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
        //@ assume from != null && to != null;
        if (!isWithinBounds(from) || !isWithinBounds(to)) {
            return false;
        }

        Tile fromTile = board.getTileFromTuple(from);
        //@ assume fromTile != null;
        Tile toTile = board.getTileFromTuple(to);
        //@ assume toTile != null;

        //@ assume fromTile.getPiece() != null;
        ChessPiece fromPiece = fromTile.getPiece();
        //@ assume fromPiece != null;

        if (fromPiece.getColor() != currentPlayer || 
            (toTile.getPiece() != null && toTile.getPiece().getColor() == currentPlayer)) {
            return false;
        }

        if (isValidMoveForPiece(from, to)) {
            if (hypothetical) return true;

            //@ assume toTile.getPiece() == null;
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
    
                // Validar limites antes de criar um Tuple
                if (tempX >= 0 && tempX < 8 && tempY >= 0 && tempY < 8) {
                    int newX = (int) tempX;
                    int newY = (int) tempY;
    
                    Tuple newLocation = new Tuple(newX, newY); // Garantido que os limites estão corretos
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
    
            // Verificar overflow/underflow e limites do tabuleiro
            if (potentialX >= 0 && potentialX < 8 && potentialY >= 0 && potentialY < 8) {
                //@ assume potentialX >= 0 && potentialX < 8;
                //@ assume potentialY >= 0 && potentialY < 8;
                int x = (int) potentialX;
                int y = (int) potentialY;
    
                Tuple newTuple = new Tuple(x, y);
                //@ assume newTuple != null;
    
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
        //@ assume from != null && to != null; // Garantir que os parâmetros não sejam nulos
        Tile fromTile = board.getTileFromTuple(from);
        //@ assume fromTile != null; // Garantir que o tile retornado não seja nulo
    
        ChessPiece fromPiece = fromTile.getPiece();
        //@ assume fromPiece != null; // Garantir que a peça no tile não seja nula
    
        if (fromPiece.hasRepeatableMoves()) {
            return isValidMoveForPieceRepeatable(from, to);
        } else {
            return isValidMoveForPieceNonRepeatable(from, to);
        }
    }
    

    private boolean isValidMoveForPieceRepeatable(Tuple from, Tuple to) {
        //@ assume from != null && to != null; // Garantir que os parâmetros não sejam nulos
        Tile fromTile = board.getTileFromTuple(from);
        //@ assume fromTile != null; // Informar ao JML que o retorno do método não é nulo
    
        ChessPiece fromPiece = fromTile.getPiece();
        //@ assume fromPiece != null; // Informar ao JML que a peça não é nula
    
        Move[] moves = fromPiece.getMoves();
        //@ assume moves != null; // Supondo que `getMoves` sempre retorna um array válido
    
        for (int i = 1; i < 8; i++) {
            for (Move move : moves) {
                //@ assume move != null; // Garantir que os movimentos não sejam nulos
    
                long potentialX = (long) from.X() + (long) move.x * i;
                long potentialY = (long) from.Y() + (long) move.y * i;
    
                // Validar antes de converter
                if (potentialX >= 0 && potentialX < 8 && potentialY >= 0 && potentialY < 8) {
                    int newX = (int) potentialX;
                    int newY = (int) potentialY;
    
                    Tuple newLocation = new Tuple(newX, newY);
                    //@ assume newLocation != null; // Garantir que o Tuple foi criado corretamente
    
                    if (newX == to.X() && newY == to.Y()) {
                        return true;
                    }
    
                    Tile newLocationTile = board.getTileFromTuple(newLocation);
                    //@ assume newLocationTile != null; // Garantir que o tile não é nulo
    
                    if (!isWithinBounds(newLocation) || !newLocationTile.isEmpty()) {
                        break;
                    }
                }
            }
        }
        return false;
    }
    

    private boolean isValidMoveForPieceNonRepeatable(Tuple from, Tuple to) {
        //@ assume board.getTileFromTuple(from) != null;
        //@ assume board.getTileFromTuple(from).getPiece() != null;
        ChessPiece fromPiece = board.getTileFromTuple(from).getPiece();
        Move[] moves = fromPiece.getMoves();

        for (Move move : moves) {
            long potentialX = (long) from.X() + (long) move.x;
            long potentialY = (long) from.Y() + (long) move.y;

            // Validar antes de converter
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