package Console;

import Chess.ChessBoard;
import Chess.Tile;

public class BoardDisplay {
    /*@ public normal_behavior
      @ requires board != null;
      @ ensures true; // Este método apenas exibe dados, não altera o estado do programa.
      @*/
    public static void printBoard(ChessBoard board){
        clearConsole();
        Tile[][] b = board.getBoardArray();

        System.out.println();
        System.out.println("      [A][B][C][D][E][F][G][H] \n");
        for(int i = 0; i < 8; i++) {
            System.out.print("[" + (8 - i) + "]   ");

            for (int j = 0; j < 8; j++){
                System.out.print(b[i][j].getValue());
            }

            System.out.println("   [" + (8 - i) + "]");
        }

        System.out.println("\n      [A][B][C][D][E][F][G][H]\n");
    }

    /**
     * Universal console clear for both Windows and Unix machines.
     */
     /*@ public normal_behavior
      @ ensures true; // Não há alteração no estado do programa, apenas no console.
      @*/
    public static void clearConsole(){
        try
        {
            final String os = System.getProperty("os.name");

            if (os.contains("Windows"))
            {
                //ASCII escape code
                System.out.print("\033[H\033[2J");
            }
            else
            {
                Runtime.getRuntime().exec("clear");
            }
        }
        catch (final Exception e){
            System.out.println("Error while trying to clear console");
        }
    }
}
